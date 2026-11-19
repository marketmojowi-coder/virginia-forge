#!/usr/bin/env python3
"""citebot: the series citation check, for any project repository.

It runs on every pull request (citebot.yml) and reads the published pages (HTML, Markdown, text) and data
(CSV, JSON) that the project lists in citebot.json.

MUST FIX (the check fails)
  holder-missing   a National Archives record group or NAID is cited and nothing near it names the holder
  working-note     working notes in published text: "(read Oct 30)", "(read for ...)", "the user's folder",
                   TODO, FIXME, "[citation needed]", "not yet confirmed"; in a citation also "to confirm", "NOTE:"
  private-pointer  a link or path a reader cannot open: file://, localhost, C:\\..., /mnt/..., claude.ai links,
                   Google Docs or Drive links
  forbidden        a name the project never uses (citebot.json "forbidden"; "Posner Library" always)

WATCH (house style: listed in the report; the check still passes unless --strict)
  iso-date, short-month, range-dash, photo-number, file-name, catalogue-title, catalogue-place, repeated,
  double-stop, dc-form, library-name, circa, m371, newspaper-holder, habs-holder, still-open
  (python3 citebot.py --rules prints what each one means)

The bot only reports. Fix at the source (the page or data-set builder) so pages, data sets and books agree.

Usage:  python3 citebot.py [--config citebot.json] [--root DIR] [--json REPORT] [--baseline FILE]
                           [--write-baseline FILE] [--strict] [--rules] [FILE ...]
Exit:   0 pass; 1 a new must-fix finding (with --strict, any new finding); 2 bad config or arguments.
Standard library only, Python 3.8 or later.
"""
import argparse, csv, fnmatch, glob, hashlib, io, json, os, re, sys
from html.parser import HTMLParser

VERSION = "1.0.0"
csv.field_size_limit(2 ** 31 - 1)

# ---------------------------------------------------------------------------------------------- rules
RULES = {   # rule: (default level, what it means and how to fix it)
    "holder-missing": ("must", "A record group or National Archives catalog number (NAID) is cited and nothing near it "
                               "names the holder. Add it to the citation, its section or row: National Archives, "
                               "Washington, D.C. (or the Library of Virginia for a Virginia record group)."),
    "working-note": ("must", "A working note is left in published text. Take it out; cite the record and its holder."),
    "private-pointer": ("must", "A link or path a reader cannot open (a file on a computer, a private link). "
                                "Cite the record and its holder instead."),
    "forbidden": ("must", "A name this project never uses."),
    "iso-date": ("watch", "A date written 1792-05-19 in a citation. House style: May 19, 1792."),
    "short-month": ("watch", "A month abbreviated in a citation. House style: write it out (September 7, 1793)."),
    "range-dash": ("watch", "A range written with a hyphen. House style: an en dash (pp. 144–145, 1791–1802)."),
    "photo-number": ("watch", "A photograph's file number is the author's own file name, not a place a reader can find. "
                              "Give the volume, page or folder, or write \u201cauthor's photograph\u201d."),
    "file-name": ("watch", "A file name in a citation. Cite the record, not the file."),
    "catalogue-title": ("watch", "A newspaper title in the Library of Congress catalogue form. House style: headline form (Daily Union)."),
    "catalogue-place": ("watch", "A place of publication in catalogue form. House style: (Washington, D.C.), (New York), (Philadelphia)."),
    "repeated": ("watch", "The same citation given twice in one place. Give it once."),
    "double-stop": ("watch", "A doubled full stop."),
    "dc-form": ("watch", "House style: Washington, D.C."),
    "library-name": ("watch", "The library's exact name: Stephen J. Ponzillo Jr. Memorial Library and Museum; A.F. & A.M."),
    "circa": ("watch", "House style: c. 1800, with a space."),
    "m371": ("watch", "The Commissioners' Proceedings are Entry 21 of Record Group 42, cited from the volumes. "
                      "Microfilm M371 is another series."),
    "newspaper-holder": ("watch", "A newspaper issue is cited without where it can be seen "
                                  "(Library of Congress, Chronicling America, or the library that holds it)."),
    "habs-holder": ("watch", "A HABS or HAER drawing or photograph is cited without its holder, the Library of Congress "
                             "(Prints and Photographs Division)."),
    "still-open": ("watch", "\u201cStill open\u201d on a published page. Owner rule: no lists of open leads."),
}
ORDER = list(RULES)

MONTHS = ["January", "February", "March", "April", "May", "June", "July", "August", "September", "October",
          "November", "December"]
SHORT = {"Jan": "January", "Feb": "February", "Mar": "March", "Apr": "April", "Jun": "June", "Jul": "July",
         "Aug": "August", "Sep": "September", "Sept": "September", "Oct": "October", "Nov": "November", "Dec": "December"}
MON = r"(?:Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)[a-z]*"
I = re.I

PRIVATE = re.compile(r"file://|\b(?:localhost|127\.0\.0\.1)\b|(?<![\w/])[A-Za-z]:\\[^\s\"<>]|/mnt/(?:project-files|user-data)\b|"
                     r"/home/user/|/tmp/claude|\bclaude\.ai/(?:artifact|code|project|chat|new)\b|\b(?:docs|drive)\.google\.com/", I)

# All published text: page text, attribute text (title, alt, aria-label, meta description) and data values.
STRONG = [
    ("working-note", re.compile(r"[(,;]\s*(?:read|seen|checked|photographed) (?:on )?" + MON + r"\.? \d{1,2}\b", I),
     "a reading date left in the text"),
    ("working-note", re.compile(r"\((?:read|pulled|photographed) for\b", I), "a \u201cread for\u201d note"),
    ("working-note", re.compile(r"\buser[\u2019']s (?:own )?(?:folder|photos?|photographs?|copy|copies|scans?|files?|pc|"
                                r"computer|drive|notes?)\b", I), "points to the user's own files, not to the holder"),
    ("working-note", re.compile(r"\b(?:TODO|FIXME|TKTK)\b"), "a to-do marker"),
    ("working-note", re.compile(r"\[(?:citation|cite|source|ref) needed\]", I), "\u201ccitation needed\u201d"),
    ("working-note", re.compile(r"\bnot yet (?:confirmed|checked|verified|read|seen|found)\b", I), "an open check"),
    ("working-note", re.compile(r"\b(?:needs?|awaiting|waiting (?:for|on)) (?:a |the |new )?(?:re-?photos?|"
                                r"photo(?:graph)?s?|check(?:ing)?|citation|source|confirmation|verification)\b", I),
     "an open task"),
    ("working-note", re.compile(r"\b(?:settled spelling|checker (?:item|note|said|flagged|found))\b", I), "a checker's note"),
    ("private-pointer", PRIVATE, "a link or path a reader cannot open"),
    ("still-open", re.compile(r"(?:^|[(\[\u2022\u00b7:;\u2014\u2013-]\s*)still open\b|\bstill open\s*(?:[:)\]]|$)", I),
     "a \u201cstill open\u201d label"),
]

# Citation text only.
CITE_NOTE = re.compile(r"\(to (?:be )?(?:confirm(?:ed)?|check(?:ed)?|verif(?:y|ied))\)|\bto be (?:confirmed|checked|verified)\b|"
                       r"\bto (?:confirm|check|verify)\s*(?:[):;]|$)|\bNOTE:|"
                       r"\b[Yy]our (?:own |[A-Z]\w* (?:[A-Z]\w* )?)?(?:photos?|photographs?|folder|files?|scans?|cop(?:y|ies)|notes?)\b")
URL = re.compile(r"\b(?:https?://|www\.)[^\s<>\"\u201d)]+", I)
QUOTED = re.compile(r'("[^"]*"|\u201c[^\u201d]*\u201d|\u2018[^\u2019]*\u2019|(?<![A-Za-z])\'[^\']*\'(?![A-Za-z]))')
KEEP = re.compile(r"\b(?:S|H|H\. ?R)\. (?:Ex\. |Misc\. )?(?:Doc|Rept|Res)\. \d+-\d+")      # S. Doc. 106-29 is a number
ISO = re.compile(r"\b(1[6-9]\d\d|20\d\d)-(0[1-9]|1[0-2])-(0[1-9]|[12]\d|3[01])\b")
SHORTM = re.compile(r"\b(Jan|Feb|Mar|Apr|Jun|Jul|Aug|Sept?|Oct|Nov|Dec)\. (\d{1,2})\b(?=[^;\"\u201c\u201d()]*?\b(?:1[6-9]|20)\d\d\b)")
RANGES = [re.compile(r"\b(1[6-9]\d\d)-(1[6-9]\d\d|\d\d)\b(?![-\u2013]\d)"),
          re.compile(r"\b(?:(?:MS )?pp?\.|MS|ff?\.|[Nn]os?\.) ?[A-Z]?\d+-[A-Z]?\d+\b"),
          re.compile(r"(?<![\w\-/.:\u2013])\d{1,4}-\d{1,4}(?![\w\-/:\u2013]|\.\d)")]
PHOTO = re.compile(r"\b(?:19|20)\d{6}_\d{6}(?:[-\u2013]\d{3,6})?\b|\bphotos? (?:no\. )?\d{3,6}\b", I)
FILENAME = re.compile(r"(?<![\w/.@-])(?:[\w-]+/)*[\w-]+\.(?:csv|json|py|src|md|xlsx?|docx?|zip|txt|jpe?g|png|tiff?|pdf)\b", I)
PLACES = {"(Washington [D.C.])": "(Washington, D.C.)", "(Washington City [D.C.])": "(Washington, D.C.)",
          "(Washington City [i.e. Washington, D.C.])": "(Washington, D.C.)", "(New-York [N.Y.])": "(New York)",
          "(Philadelphia [Pa.])": "(Philadelphia)"}
FIXED = [("double-stop", re.compile(r"(?<!\.)\.\.(?!\.)"), "a doubled full stop", lambda m: "."),
         ("dc-form", re.compile(r"\bWashington, DC\b"), "Washington, D.C.", lambda m: "Washington, D.C."),
         ("library-name", re.compile(r"\bPonzillo, Jr\.?"), "the library's exact name", lambda m: "Ponzillo Jr."),
         ("library-name", re.compile(r"\bA\.F\.&A\.M\."), "the Grand Lodge's exact name", lambda m: "A.F. & A.M."),
         ("circa", re.compile(r"\bc\.(\d)"), "c. with a space", lambda m: "c. " + m.group(1))]
SMALL = {"of", "the", "and", "a", "an", "in", "for", "on", "at", "to", "or"}
TITLE = re.compile(r"((?:The )?[A-Z][A-Za-z\-]*(?: [A-Za-z\-]+)*?)(\.)?(?=(?: \([^()]*\))?, (?:1[6-9]|20)\d\d-\d\d-\d\d\b)")

# Holders
RG = re.compile(r"\b(?:RG|R\.G\.|Record Groups?|RGs) ?(\d{1,3}(?:(?:, and |, | and | & )\d{1,3})*)\b")
NAID = re.compile(r"\bNAID:? ?\d+")
NARA = re.compile(r"National Archives|\bNARA\b|archives\.gov", I)
RG_HELD = re.compile(r"National Archives|\bNARA\b|archives\.gov|Library of Virginia|lva\.virginia\.gov|State Library|"
                     r"State Archives|Archives of (?:Maryland|Virginia)", I)        # state record groups have state holders
PAPER = re.compile(r"\b(?:National Intelligencer|Evening Star|Sunday Star|Washington Critic|Patowmack Packet|City Gazette|"
                   r"Impartial Observer|Cent(?:inel|ennial) of Liberty|Sentinel of Liberty|Gazette of the United[- ]States|"
                   r"Columbian Mirror|Washington Gazette|Washington Federalist|Universal Gazette|Daily Union|Madisonian|"
                   r"(?:[A-Z][\w'\u2019]*[ -])*(?:Gazette|Intelligencer|Advertiser|Herald|Enquirer|Spectator|Argus|"
                   r"Centinel|Sentinel|Observer|Mirror|Packet|Courier|Chronicle|Journal|Republican|Register|Messenger|"
                   r"Repository|Ledger|Telegraph|Globe|Aurora|Times|Tribune|Post|Patriot|Recorder|Monitor|Sun))\b")
PAPER_DATE = re.compile(r"\b" + MON + r"\.? \d{1,2},? (?:1[6-9]|20)\d\d\b|\b(?:1[6-9]|20)\d\d-\d\d-\d\d\b")
NEWS_HELD = re.compile(r"Library of Congress|Chronicling America|loc\.gov|Harvard|Library Society|Antiquarian|Readex|"
                       r"microfilm|Historical Society|Library|Archives|newspapers\.com|genealogybank", I)
HABS = re.compile(r"\bHA(?:BS|ER|LS)\b")
HABS_HELD = re.compile(r"Library of Congress|loc\.gov", I)
HELD = {"rg": RG_HELD, "naid": NARA, "news": NEWS_HELD, "habs": HABS_HELD}
NEED_RULE = {"rg": "holder-missing", "naid": "holder-missing", "news": "newspaper-holder", "habs": "habs-holder"}

# What makes a line of a page a citation
SIGNAL = re.compile(r"\b(?:RG|Record Groups?) ?\d|National Archives|\bNARA\b|Library of Congress|Chronicling America|"
                    r"\bNAID\b|\bHA(?:BS|ER)\b|\bMS pp?\.|\bEntry \d|\bvol\. \d|Ponzillo|Historical Society|"
                    r"Library Society|University Library|\bArchives\b|\bLCCN\b")


def needs(text):
    """What holders a piece of text needs: [(kind, key, match, start)]."""
    out = []
    for m in RG.finditer(text):
        for n in re.findall(r"\d+", m.group(1)): out.append(("rg", n, m.group(0), m.start()))
    for m in NAID.finditer(text): out.append(("naid", "naid", m.group(0), m.start()))
    for m in PAPER.finditer(text):
        if PAPER_DATE.search(text, m.end(), m.end() + 100):
            out.append(("news", re.sub(r"^(?:The|Daily) ", "", m.group(0)).lower(), m.group(0), m.start())); break
    for m in HABS.finditer(text):
        out.append(("habs", "habs", m.group(0), m.start())); break
    return out


def has_need(text, kind, key):
    return any(k == kind and v == key for k, v, _, _ in needs(text))


def paper_title(t):
    w = t.rstrip(".").split()
    w = [x if i and x.lower() in SMALL else "-".join(p[:1].upper() + p[1:] for p in x.split("-")) for i, x in enumerate(w)]
    return " ".join(w[1:] if w[0] == "The" and len(w) > 2 else w)


def split_top(s):
    parts, depth, cur = [], 0, ""
    for i, ch in enumerate(s):
        depth += ch in "(\u201c["; depth -= ch in ")\u201d]"
        if ch == ";" and depth <= 0 and s[i + 1:i + 2] == " ": parts.append(cur); cur = ""; continue
        cur += ch
    return parts + [cur]


def repeats(s):
    """Parts of a citation given twice (or a shorter copy of a fuller one): [(part, start)]."""
    parts, pos, out = [], 0, []
    for p in split_top(s):
        lead = len(p) - len(p.lstrip())
        parts.append((p.strip(), pos + lead)); pos += len(p) + 1
    names = [p for p, _ in parts]
    if len(names) < 2: return out
    keep = []
    for i, (p, at) in enumerate(parts):
        if not p: continue
        if p in keep or any(j != i and q.startswith(p + ", ") for j, q in enumerate(names)): out.append((p, at)); continue
        keep.append(p)
    return out


def excerpt(text, start, length, width=48):
    a, b = max(0, start - width), min(len(text), start + length + width)
    return ("\u2026" if a else "") + text[a:b] + ("\u2026" if b < len(text) else "")


# ---------------------------------------------------------------------------------------------- units
class Unit:
    """One piece of published text: a block of a page, a data cell, a JSON value or an attribute."""
    def __init__(self, file, line, text, cite=False, kind="text", where="", resolve=None):
        self.file, self.line, self.text, self.cite, self.kind = file, line, text, cite, kind
        self.where, self.resolve = where, resolve   # a data path (stones[3].srcs[0]); a lazy line finder
        self.marks = [(0, line)]          # (offset in text, source line)
        self.links = []                   # hrefs inside this block (pages)
        self.window = ""                  # where the holder may also be named (a data row or object)
        self.node = None                  # its block on a page

    def line_at(self, pos):
        if self.line is None:
            self.line = self.resolve() if self.resolve else 1
            self.marks = [(0, self.line)]
        line = self.line
        for off, ln in self.marks:
            if off <= pos: line = ln
            else: break
        return line


# ---------------------------------------------------------------------------------------------- the bot
class Bot:
    def __init__(self, cfg, root):
        self.cfg, self.root = cfg, root
        self.name = cfg.get("name") or os.path.basename(os.path.abspath(root))
        lv = {r: RULES[r][0] for r in RULES}
        for r, v in (cfg.get("severity") or {}).items():
            if r not in RULES or v not in ("must", "watch", "off"): raise ValueError("severity: unknown rule or level: %s=%s" % (r, v))
            lv[r] = v
        for r in cfg.get("off") or []:
            if r not in RULES: raise ValueError("off: unknown rule %s" % r)
            lv[r] = "off"
        self.level = lv
        forb = {"Posner Library": "The library is the Stephen J. Ponzillo Jr. Memorial Library and Museum."}
        forb.update(cfg.get("forbidden") or {})
        self.forbidden = [(re.compile(("\\b" if p[:1].isalnum() else "") + re.escape(p) + ("\\b" if p[-1:].isalnum() else ""), I),
                           p, msg) for p, msg in forb.items()]
        self.csv_cols = re.compile(cfg.get("csv_columns") or r"^(source|sources|citation|citations|cite|book note|.*_cite|"
                                   r".*_source|holder|held|credit|credits|reference|references)$", I)
        self.json_keys = re.compile(cfg.get("json_keys") or r"^(source|sources|src|srcs|citation|citations|cite|cites|"
                                    r".*_cite|.*Cite|holder|held|credit|credits|ref|refs|reference|references)$", I)
        self.skip_cols = re.compile(cfg["skip_columns"], I) if cfg.get("skip_columns") else None
        self.skip_keys = re.compile(cfg["skip_keys"], I) if cfg.get("skip_keys") else None
        self.html_cite = re.compile(cfg.get("html_cite_class") or r"(?:^|[\s_-])(?:cite|cites|citation|citations|source|"
                                    r"sources|src|note|notes|ref|refs|references|credit|credits|footnote|footnotes|fn)"
                                    r"(?:$|[\s_-])", I)
        self.findings, self.seen = [], {}
        self.files = self.units = self.cites = 0

    # -- findings
    def add(self, rule, unit, start, match, note, fix=None):
        level = self.level[rule]
        if level == "off": return
        line = unit.line_at(start)
        ex = excerpt(unit.text, start, len(match))
        key = (unit.file, line, rule, match, ex)
        if key in self.seen:
            self.seen[key]["more"] += 1; return
        fp = hashlib.sha1("\x1f".join([rule, unit.file, match, re.sub(r"\s+", " ", ex)]).encode("utf-8")).hexdigest()[:16]
        self.findings.append({"file": unit.file, "line": line, "rule": rule, "level": level, "match": match,
                              "fix": fix, "note": note, "excerpt": ex, "fp": fp, "known": False, "where": unit.where, "more": 0})
        self.seen[key] = self.findings[-1]

    # -- text rules
    def check_text(self, unit, links_only=False):
        t = unit.text
        if links_only:
            for m in PRIVATE.finditer(t): self.add("private-pointer", unit, m.start(), m.group(0), "a link a reader cannot open")
            return
        self.units += 1
        for rule, rx, note in STRONG:
            for m in rx.finditer(t): self.add(rule, unit, m.start(), m.group(0), note)
        for rx, p, msg in self.forbidden:
            for m in rx.finditer(t): self.add("forbidden", unit, m.start(), m.group(0), msg)
        if unit.cite: self.check_cite(unit)

    def check_cite(self, unit):
        self.cites += 1
        t = URL.sub(lambda m: " " * len(m.group(0)), unit.text)        # links are not citation text
        quoted = [m.span() for m in QUOTED.finditer(t)]
        kept = [m.span() for m in KEEP.finditer(t)]
        inside = lambda p, spans: any(a <= p < b for a, b in spans)

        def hit(rule, start, match, note, fix=None):
            if not inside(start, quoted): self.add(rule, unit, start, match, note, fix)

        if unit.kind == "data" or SIGNAL.search(t):         # cited text, not a page's own instructions
            for m in CITE_NOTE.finditer(t): hit("working-note", m.start(), m.group(0), "a working note in a citation")
        for m in ISO.finditer(t):
            hit("iso-date", m.start(), m.group(0), "date as Month D, YYYY",
                "%s %d, %s" % (MONTHS[int(m.group(2)) - 1], int(m.group(3)), m.group(1)))
        for m in SHORTM.finditer(t):
            hit("short-month", m.start(), m.group(0), "month written out", SHORT[m.group(1)] + " " + m.group(2))
        done = set()
        for rx in RANGES:
            for m in rx.finditer(t):
                h = m.start() + m.group(0).index("-")
                if h in done or inside(h, kept) or ISO.match(t, max(0, h - 4)) or ISO.match(t, max(0, h - 7)): continue
                done.add(h); hit("range-dash", m.start(), m.group(0), "en dash in a range", m.group(0).replace("-", "\u2013"))
        for m in PHOTO.finditer(t): hit("photo-number", m.start(), m.group(0), "a photograph file number")
        for m in FILENAME.finditer(t): hit("file-name", m.start(), m.group(0), "a file name")
        pos = 0
        for p in split_top(t):
            q = p.lstrip(); m = TITLE.match(q)
            if m and paper_title(m.group(1)) != m.group(0):
                at = pos + len(p) - len(q)
                hit("catalogue-title", at, m.group(0), "newspaper title in headline form", paper_title(m.group(1)))
            pos += len(p) + 1
        for a, b in PLACES.items():
            for m in re.finditer(re.escape(a), t): hit("catalogue-place", m.start(), a, "place as the books give it", b)
        for p, at in repeats(t): hit("repeated", at, p, "the same citation twice", "give it once")
        for rule, rx, note, f in FIXED:
            for m in rx.finditer(t): hit(rule, m.start(), m.group(0), note, f(m))
        if re.search(r"\bM-?371\b", t) and "Proceedings" in t:
            m = re.search(r"\bM-?371\b", t); hit("m371", m.start(), m.group(0), "Proceedings cited as microfilm M371")

    # -- holders
    def holder(self, unit, page_units=None, levels=3):
        """Every record group, NAID, newspaper issue or HABS sheet cited in the unit must have its holder named in
        the unit, its row or object (data), its part of the page (up to three blocks up), or, on a page, in another
        line that names the same record group with its holder."""
        for kind, key, match, start in needs(unit.text):
            rx = HELD[kind]
            if rx.search(unit.text) or any(rx.search(h) for h in unit.links) or (unit.window and rx.search(unit.window)):
                continue
            ok, n, up = False, unit.node, 0
            while n is not None and n.parent is not None and up < levels:
                n = n.parent; up += 1
                if n.tag in ("#root", "html", "body", "main"): break
                if rx.search(n.full()) or any(rx.search(h) for h in n.all_links()): ok = True; break
            if not ok and page_units:
                ok = any(u is not unit and rx.search(u.text) and has_need(u.text, kind, key) for u in page_units)
            if ok: continue
            if kind == "rg": note = "Record Group %s is cited and its holder (the National Archives) is not named" % key
            elif kind == "naid": note = "a National Archives catalog number without the holder named"
            elif kind == "news": note = "newspaper issue without where it can be seen"
            else: note = "HABS/HAER item without its holder (Library of Congress)"
            self.add(NEED_RULE[kind], unit, start, match, note)

    # -- files
    def check_file(self, rel):
        path = os.path.join(self.root, rel)
        ext = os.path.splitext(rel)[1].lower()
        try:
            with open(path, encoding="utf-8-sig", errors="replace") as fh: raw = fh.read()
        except OSError as e:
            print("citebot: cannot read %s: %s" % (rel, e), file=sys.stderr); return
        self.files += 1
        if ext in (".html", ".htm"): self.check_html(rel, raw)
        elif ext in (".md", ".markdown", ".txt"): self.check_prose(rel, raw, ext != ".txt")
        elif ext == ".csv": self.check_csv(rel, raw)
        elif ext == ".json": self.check_json(rel, raw)

    def check_html(self, rel, raw):
        p = Page(self.html_cite)
        try:
            p.feed(raw); p.close()
        except Exception as e:      # html.parser is lenient; this is only a guard
            print("citebot: %s: could not read the page (%s)" % (rel, e), file=sys.stderr)
        units = []
        for n in p.blocks:
            text = n.text()
            if not text: continue
            u = Unit(rel, n.line, text, cite=n.cite or bool(SIGNAL.search(text)))
            u.marks, u.links, u.node = n.marks, n.links, n
            units.append(u)
        for u in units: self.check_text(u)
        for u in units: self.holder(u, units)
        for line, text, kind in p.attrs:
            self.check_text(Unit(rel, line, text, kind="attr"), links_only=(kind == "link"))

    def check_prose(self, rel, raw, markdown):
        units, sec, code, buf, start = [], Section(), False, [], 0
        sections = [sec]

        def flush():
            if buf:
                text = re.sub(r"\s+", " ", " ".join(buf)).strip()
                if markdown:
                    links = re.findall(r"\]\(([^)\s]+)", text)
                    text = re.sub(r"!?\[([^\]]*)\]\([^)]*\)", r"\1", text)
                else: links = []
                if text:
                    u = Unit(rel, start, text, cite=bool(SIGNAL.search(text) or re.match(r"\[\^[^\]]+\]:", text)
                                                         or sec.cite))
                    u.links, u.node = links, sec.add(u)
                    units.append(u)
            buf.clear()

        for i, line in enumerate(raw.split("\n"), 1):
            s = line.strip()
            if markdown and re.match(r"^(```|~~~)", s): flush(); code = not code; continue
            if code: continue
            if markdown and s.startswith("#"):
                flush(); sec = Section(re.sub(r"^#+\s*", "", s)); sections.append(sec)
                u = Unit(rel, i, sec.title); units.append(u); u.node = sec.add(u); continue
            if not s or (markdown and re.match(r"^([-*+]|\d+[.)])\s", s)): flush()
            if s:
                if not buf: start = i
                buf.append(re.sub(r"<!--.*?-->", "", s))
        flush()
        for u in units: self.check_text(u)
        for u in units: self.holder(u, units, levels=1)
        for u in units:
            for h in u.links: self.check_text(Unit(rel, u.line, h, kind="link"), links_only=True)

    def check_csv(self, rel, raw):
        rows = csv.reader(io.StringIO(raw, newline=""))
        try:
            head = next(rows)
        except StopIteration:
            return
        cites = [bool(self.csv_cols.match(h.strip())) for h in head]
        skip = [bool(self.skip_cols and self.skip_cols.match(h.strip())) for h in head]
        prev = rows.line_num
        for row in rows:
            first, prev = prev + 1, rows.line_num
            window = " ; ".join(row)
            for j, v in enumerate(row):
                if not v.strip() or (j < len(skip) and skip[j]): continue
                cite = j < len(cites) and cites[j]
                u = Unit(rel, first, v.strip(), cite=cite, kind="data", where=head[j].strip() if j < len(head) else "column %d" % (j + 1))
                u.window = window
                self.check_text(u)
                if cite: self.holder(u)

    def check_json(self, rel, raw):
        try:
            data = json.loads(raw)
        except ValueError as e:
            print("citebot: %s is not valid JSON (%s); skipped" % (rel, e), file=sys.stderr); return
        flat = raw.count("\n") < 3            # one-line (minified) JSON: every value is on line 1

        def line_of(s):
            if flat: return 1
            at = -1
            for enc in (json.dumps(s, ensure_ascii=False)[1:-1], json.dumps(s)[1:-1]):
                at = raw.find(enc)
                if at >= 0: break
            return raw.count("\n", 0, at) + 1 if at >= 0 else 1

        def walk(o, cite, window, path):
            if isinstance(o, dict):
                win = " ; ".join(v if isinstance(v, str) else " ; ".join(x for x in v if isinstance(x, str))
                                 for v in o.values() if isinstance(v, (str, list)))
                for k, v in o.items():
                    if self.skip_keys and self.skip_keys.match(str(k)): continue
                    walk(v, cite or bool(self.json_keys.match(str(k))), win, "%s.%s" % (path, k) if path else str(k))
            elif isinstance(o, list):
                for i, x in enumerate(o): walk(x, cite, window, "%s[%d]" % (path, i))
            elif isinstance(o, str) and o.strip():
                u = Unit(rel, None, o.strip(), cite=cite, kind="data", where=path, resolve=lambda s=o: line_of(s))
                u.window = window
                self.check_text(u)
                if cite: self.holder(u)

        walk(data, False, "", "")

    # -- run
    def targets(self, only=None):
        inc = self.cfg.get("include") or ["**/*.html", "**/*.htm", "**/*.csv", "**/*.json"]
        exc = list(self.cfg.get("exclude") or []) + [".git/**", "**/node_modules/**", "node_modules/**", "citebot/**",
                                                      ".github/**", "**/package.json", "**/package-lock.json"]
        found = set()
        for pat in inc:
            for f in glob.glob(os.path.join(self.root, pat), recursive=True):
                if os.path.isfile(f): found.add(os.path.relpath(f, self.root).replace(os.sep, "/"))
        if only is not None:
            found = {os.path.relpath(os.path.join(self.root, f) if not os.path.isabs(f) else f, self.root).replace(os.sep, "/")
                     for f in only} & found
        return sorted(f for f in found if not any(fnmatch.fnmatch(f, x) for x in exc))

    def run(self, only=None):
        for rel in self.targets(only): self.check_file(rel)
        rank = {"must": 0, "watch": 1}
        self.findings.sort(key=lambda f: (rank[f["level"]], f["file"], f["line"], ORDER.index(f["rule"])))
        return self.findings


class Section:
    """A heading's part of a Markdown or text file (stands in for a page block when looking for a holder)."""
    tag = "section"

    def __init__(self, title=""):
        self.title, self.units, self.parent = title, [], None
        self.cite = bool(re.match(r"(sources|notes|references|citations|credits|bibliography)\b", title, I))

    def add(self, u):
        self.units.append(u)
        return _Leaf(self)

    def full(self):
        return " ".join(u.text for u in self.units)

    def all_links(self):
        return [h for u in self.units for h in u.links]


class _Leaf:
    def __init__(self, sec): self.parent, self.tag = sec, "p"


# ---------------------------------------------------------------------------------------------- pages
BLOCK = set("address article aside blockquote body caption dd details dialog div dl dt fieldset figcaption figure footer "
            "form h1 h2 h3 h4 h5 h6 header hgroup html li main nav ol p pre section summary table tbody td tfoot th thead "
            "tr ul title svg g text desc noscript".split())
CITE_TAGS = {"cite", "figcaption", "small", "sup", "footer", "aside", "caption"}
VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "param", "source", "track", "wbr"}
SKIP = {"script", "style", "template"}
TEXT_ATTRS = {"title", "alt", "aria-label", "aria-description", "placeholder", "label"}
LINK_ATTRS = {"href", "src", "action", "poster", "data", "cite", "formaction", "background", "srcset", "xlink:href"}
META_TEXT = {"description", "og:description", "og:title", "twitter:title", "twitter:description", "keywords", "author"}
CLOSES_P = BLOCK - {"body", "html", "title", "svg", "g", "text", "desc", "noscript", "caption", "td", "th", "tr", "tbody",
                    "thead", "tfoot", "li", "dd", "dt", "summary"} | {"hr"}


class Node:
    def __init__(self, tag, attrs, parent, line):
        self.tag, self.attrs, self.parent, self.line = tag, attrs, parent, line
        self.kids, self.parts, self.marks, self.links = [], [], [], []
        self.cite = self.soft = False
        self._full = None

    def add(self, data, line):
        s = re.sub(r"\s+", " ", data)
        cur = "".join(self.parts)
        if not cur or cur.endswith(" "): s = s.lstrip()
        if not s: return
        if self.soft and s[:1].isalnum() and re.search(r"[\w.;:)\]]$", cur):
            s = " " + s                   # <span>Design competition</span><small>National Gazette ...: two phrases
        self.soft = False
        self.marks.append((len(cur), line))
        self.parts.append(s)

    def text(self):
        return "".join(self.parts).strip()

    def full(self):
        if self._full is None: self._full = " ".join([self.text()] + [k.full() for k in self.kids]).strip()
        return self._full

    def all_links(self):
        return self.links + [h for k in self.kids for h in k.all_links()]


class Page(HTMLParser):
    def __init__(self, cite_rx):
        super().__init__(convert_charrefs=True)
        self.cite_rx = cite_rx
        self.root = Node("#root", {}, None, 1)
        self.stack = [(self.root, True, False)]            # (node or tag, is block, is cite-like)
        self.blocks, self.attrs, self.skip = [], [], 0

    def _block(self):
        for n, b, _ in reversed(self.stack):
            if b: return n
        return self.root

    def _is_cite(self, tag, a):
        cls = " ".join([a.get("class", ""), a.get("id", ""), a.get("role", "")])
        return tag in CITE_TAGS or bool(cls.strip() and self.cite_rx.search(cls)) or a.get("role") == "doc-endnotes"

    def _close(self, tag):
        names = [n.tag if isinstance(n, Node) else n for n, _, _ in self.stack]
        if tag not in names[1:]: return
        while len(self.stack) > 1:
            n, _, _ = self.stack.pop()
            if (n.tag if isinstance(n, Node) else n) == tag: break

    def _open(self, tag):
        names = [n.tag if isinstance(n, Node) else n for n, _, _ in self.stack]
        if tag in CLOSES_P and "p" in names and not any(x in names[names.index("p"):] for x in ("table", "button")):
            self._close("p")
        if tag in ("li", "dt", "dd") and names:
            for t in reversed(names):
                if t in ("ul", "ol", "dl", "menu"): break
                if t in ("li", "dt", "dd"): self._close(t); break
        if tag == "tr":
            for t in reversed(names):
                if t in ("table", "tbody", "thead", "tfoot"): break
                if t == "tr": self._close("tr"); break
        if tag in ("td", "th"):
            for t in reversed(names):
                if t in ("tr", "table", "tbody", "thead", "tfoot"): break
                if t in ("td", "th"): self._close(t); break

    def handle_starttag(self, tag, attrs):
        line = self.getpos()[0]
        a = {k: (v or "") for k, v in attrs}
        for k, v in a.items():
            if not v.strip(): continue
            if k in TEXT_ATTRS: self.attrs.append((line, v.strip(), "text"))
            elif k in LINK_ATTRS: self.attrs.append((line, v.strip(), "link"))
        if tag == "meta" and (a.get("name", "").lower() in META_TEXT or a.get("property", "").lower() in META_TEXT) \
                and a.get("content", "").strip():
            self.attrs.append((line, a["content"].strip(), "text"))
        if tag in SKIP: self.skip += 1; self.stack.append((tag, False, False)); return
        if tag == "br": self._block().add(" ", line); return
        if tag in VOID: return
        self._open(tag)
        cite = self._is_cite(tag, a)
        if tag in BLOCK:
            parent = self._block()
            n = Node(tag, a, parent, line)
            parent.kids.append(n); self.blocks.append(n)
            self.stack.append((n, True, cite))
        else:
            self.stack.append((tag, False, cite))
            self._block().soft = True
        if tag == "a" and a.get("href"): self._block().links.append(a["href"])

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in VOID and tag != "br": self.handle_endtag(tag)

    def handle_endtag(self, tag):
        if tag in SKIP:
            if self.skip: self.skip -= 1
        self._close(tag)
        if tag not in BLOCK: self._block().soft = True

    def handle_data(self, data):
        if self.skip: return
        b = self._block()
        b.add(data, self.getpos()[0])
        if data.strip() and any(c for _, _, c in self.stack): b.cite = True


# ---------------------------------------------------------------------------------------------- report
def esc_prop(s): return s.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A").replace(":", "%3A").replace(",", "%2C")
def esc_msg(s): return s.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
def cell(s, n=140):
    s = re.sub(r"\s+", " ", str(s or "")).replace("|", "\\|")
    return s if len(s) <= n else s[:n - 1] + "\u2026"


def summary_md(bot, new, known, strict):
    must = [f for f in new if f["level"] == "must"]
    watch = [f for f in new if f["level"] == "watch"]
    fail = bool(must or (strict and watch))
    L = ["## Citations: %s" % ("FAIL" if fail else "PASS"), "",
         "%s \u00b7 citebot %s \u00b7 %d files checked: %d citations among %d pieces of text." % (
             bot.name, VERSION, bot.files, bot.cites, bot.units), ""]
    if not new and not known:
        L += ["No findings: every cited record names its holder, and no working notes or house-style slips were found.", ""]
    counts = {}
    for f in new: counts.setdefault(f["rule"], [0, 0])[0 if f["level"] == "must" else 1] += 1
    if counts:
        L += ["| Rule | Must fix | Watch | What it means |", "|---|---:|---:|---|"]
        for r in ORDER:
            if r in counts: L.append("| %s | %d | %d | %s |" % (r, counts[r][0], counts[r][1], cell(RULES[r][1], 200)))
        L.append("")

    def table(items, cap=200):
        T = ["| Where | Rule | Found | Text | Fix |", "|---|---|---|---|---|"]
        for f in items[:cap]:
            where = "%s:%d%s%s" % (f["file"], f["line"], (" " + f["where"]) if f["where"] else "",
                                   (" (+%d more)" % f["more"]) if f["more"] else "")
            T.append("| %s | %s | %s | %s | %s |" % (cell(where, 110), f["rule"], cell(f["match"], 60),
                                                   cell(f["excerpt"]), cell(f["fix"] or f["note"], 80)))
        if len(items) > cap: T.append("| \u2026 | | %d more in the JSON report | | |" % (len(items) - cap))
        return T

    if must: L += ["### Must fix (%d)" % len(must), ""] + table(must) + [""]
    if watch:
        L += ["### Watch: house style (%d)" % len(watch), "", "<details><summary>Show the list</summary>", ""] + table(watch) + ["", "</details>", ""]
    if known:
        km = sum(1 for f in known if f["level"] == "must")
        L += ["Known before the bot was installed (baseline): %d must fix, %d watch. They do not fail the check; "
              "the JSON report lists them." % (km, len(known) - km), ""]
    return "\n".join(L)


def main(argv=None):
    ap = argparse.ArgumentParser(description="Series citation check (citebot %s)." % VERSION)
    ap.add_argument("files", nargs="*", help="check only these files (paths from --root)")
    ap.add_argument("--config", default=None, help="citebot.json (default: citebot/citebot.json or citebot.json if present)")
    ap.add_argument("--root", default=".", help="the repository root (default: .)")
    ap.add_argument("--json", dest="json_out", help="write the full report here")
    ap.add_argument("--summary", help="write the Markdown summary here (in GitHub Actions it also goes to the job summary)")
    ap.add_argument("--baseline", help="findings recorded here are known and do not fail the check")
    ap.add_argument("--write-baseline", help="record every finding now as known, then exit 0")
    ap.add_argument("--strict", action="store_true", help="watch findings fail the check too")
    ap.add_argument("--rules", action="store_true", help="list the rules and exit")
    ap.add_argument("--quiet", action="store_true", help="print only the totals")
    a = ap.parse_args(argv)
    if a.rules:
        for r in ORDER: print("%-16s %-5s  %s" % (r, RULES[r][0], RULES[r][1]))
        return 0
    cfgp = a.config
    if cfgp is None:
        for c in ("citebot/citebot.json", "citebot.json"):
            if os.path.isfile(os.path.join(a.root, c)): cfgp = os.path.join(a.root, c); break
    try:
        cfg = {}
        if cfgp:
            with open(cfgp, encoding="utf-8") as fh: cfg = json.load(fh)
        bot = Bot(cfg, a.root)
    except (OSError, ValueError) as e:
        print("citebot: bad config %s: %s" % (cfgp, e), file=sys.stderr); return 2
    basep = a.baseline or (cfg.get("baseline") and os.path.join(a.root, cfg["baseline"]))
    known_fp = set()
    if basep and not a.write_baseline and os.path.isfile(basep):
        try:
            with open(basep, encoding="utf-8") as fh: known_fp = set(json.load(fh).get("known", []))
        except (OSError, ValueError) as e:
            print("citebot: bad baseline %s: %s" % (basep, e), file=sys.stderr); return 2
    findings = bot.run(a.files or None)
    if a.write_baseline:
        with open(a.write_baseline, "w", encoding="utf-8") as fh:
            json.dump({"citebot": VERSION, "note": "Findings known when the bot was installed. They are listed but do not "
                       "fail the check. Fix them at the source, then rewrite this file.",
                       "known": sorted({f["fp"] for f in findings})}, fh, indent=1)
        print("citebot: %d findings recorded as known in %s" % (len(findings), a.write_baseline))
        return 0
    for f in findings: f["known"] = f["fp"] in known_fp
    new = [f for f in findings if not f["known"]]
    known = [f for f in findings if f["known"]]
    must = [f for f in new if f["level"] == "must"]
    fail = bool(must or (a.strict and new))
    if not a.quiet:
        for f in new:
            print("%-5s %s:%d%s %s: %s  [%s]%s%s" % (f["level"].upper(), f["file"], f["line"], (" " + f["where"]) if f["where"] else "",
                                                  f["rule"], f["match"], f["note"], ("  fix: " + f["fix"]) if f["fix"] else "",
                                                  ("  (+%d more)" % f["more"]) if f["more"] else ""))
    print("citebot %s: %s. %d files; %d must fix, %d watch%s." % (
        VERSION, "FAIL" if fail else "PASS", bot.files, len(must), len(new) - len(must),
        (", %d known (baseline)" % len(known)) if known else ""))
    if os.environ.get("GITHUB_ACTIONS") == "true":
        for f in (must + [f for f in new if f["level"] == "watch"])[:50]:
            print("::%s file=%s,line=%d,title=%s::%s" % ("error" if f["level"] == "must" else "warning", esc_prop(f["file"]),
                  f["line"], esc_prop("citebot " + f["rule"]), esc_msg("%s: %s%s" % (f["note"], f["match"],
                                                                                      (" \u2192 " + f["fix"]) if f["fix"] else ""))))
    md = summary_md(bot, new, known, a.strict)
    for p in filter(None, [a.summary, os.environ.get("GITHUB_STEP_SUMMARY")]):
        with open(p, "a", encoding="utf-8") as fh: fh.write(md + "\n")
    if a.json_out:
        with open(a.json_out, "w", encoding="utf-8") as fh:
            json.dump({"citebot": VERSION, "name": bot.name, "pass": not fail, "files": bot.files, "units": bot.units,
                       "citations": bot.cites, "rules": {r: {"level": bot.level[r], "means": RULES[r][1]} for r in ORDER},
                       "findings": findings}, fh, ensure_ascii=False, indent=1)
    return 1 if fail else 0


if __name__ == "__main__":
    sys.exit(main())
