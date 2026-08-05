#!/usr/bin/env python3
"""Live poll + Q&A for the ChemE Chula orientation deck. One file, no install.

    python3 orientation-live.py --deck orientation-2569-all-years.html

It prints a QR. Students scan it, the phone opens a page served by THIS laptop
over the room's own network, they tap an answer or type a question, and the deck
updates within a second. Votes and questions live in memory and are mirrored to
live-results.json, so a crash mid-session loses nothing.

    --port 8080          change the port
    --room CHE69         the room code students see and type (default: random)
    --deck <file.html>   point that deck at this server and serve it at /deck
    --hotspot-help       what to do when campus wifi blocks phone-to-laptop

Python 3.8+, standard library only. The QR encoder is included (qrlite below),
so there is nothing to pip install five minutes before the session.
"""
import argparse
import json
import pathlib
import random
import re
import socket
import string
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

# ══════════════════════════════════════════════════════════════════════
# qrlite — byte mode, ECC level M, versions 1-10. Verified against a
# reference decoder; enough for a LAN URL and nothing more.
# ══════════════════════════════════════════════════════════════════════
SPEC = {1: (16, 10, (1, 16, 0, 0)), 2: (28, 16, (1, 28, 0, 0)),
        3: (44, 26, (1, 44, 0, 0)), 4: (64, 18, (2, 32, 0, 0)),
        5: (86, 24, (2, 43, 0, 0)), 6: (108, 16, (4, 27, 0, 0)),
        7: (124, 18, (4, 31, 0, 0)), 8: (154, 22, (2, 38, 2, 39)),
        9: (182, 22, (3, 36, 2, 37)), 10: (216, 26, (4, 43, 1, 44))}
ALIGN = {1: [], 2: [6, 18], 3: [6, 22], 4: [6, 26], 5: [6, 30], 6: [6, 34],
         7: [6, 22, 38], 8: [6, 24, 42], 9: [6, 26, 46], 10: [6, 28, 50]}
VERSION_BITS = {7: 0x07C94, 8: 0x085BC, 9: 0x09A99, 10: 0x0A4D3}
EXP, LOG, _x = [0] * 512, [0] * 256, 1
for _i in range(255):
    EXP[_i] = _x
    LOG[_x] = _i
    _x <<= 1
    if _x & 0x100:
        _x ^= 0x11D
for _i in range(255, 512):
    EXP[_i] = EXP[_i - 255]


def _mul(a, b):
    return 0 if a == 0 or b == 0 else EXP[LOG[a] + LOG[b]]


def _gen_poly(n):
    g = [1]
    for i in range(n):
        nxt = [0] * (len(g) + 1)
        for j, c in enumerate(g):
            nxt[j] ^= c
            nxt[j + 1] ^= _mul(c, EXP[i])
        g = nxt
    return g


def _ec(block, n):
    g, rem = _gen_poly(n), list(block) + [0] * n
    for i in range(len(block)):
        c = rem[i]
        if c:
            for j in range(len(g)):
                rem[i + j] ^= _mul(g[j], c)
    return rem[len(block):]


def _cw(data, version):
    total, b = SPEC[version][0], []

    def put(v, n):
        for k in range(n - 1, -1, -1):
            b.append((v >> k) & 1)

    put(0b0100, 4)
    put(len(data), 8 if version < 10 else 16)
    for byte in data:
        put(byte, 8)
    for _ in range(min(4, total * 8 - len(b))):
        b.append(0)
    while len(b) % 8:
        b.append(0)
    cw = [int("".join(str(x) for x in b[i:i + 8]), 2) for i in range(0, len(b), 8)]
    n0 = len(cw)
    while len(cw) < total:
        cw.append([0xEC, 0x11][(len(cw) - n0) % 2])
    return cw


def _interleave(cw, version):
    _, ecn, (n1, s1, n2, s2) = SPEC[version]
    blocks, ecs, at = [], [], 0
    for n, s in ((n1, s1), (n2, s2)):
        for _ in range(n):
            blk = cw[at:at + s]
            at += s
            blocks.append(blk)
            ecs.append(_ec(blk, ecn))
    out = []
    for i in range(max(len(b) for b in blocks)):
        out += [b[i] for b in blocks if i < len(b)]
    for i in range(ecn):
        out += [e[i] for e in ecs]
    return out


def _template(version):
    n = version * 4 + 17
    m = [[0] * n for _ in range(n)]

    def finder(r, c):
        for dr in range(-1, 8):
            for dc in range(-1, 8):
                rr, cc = r + dr, c + dc
                if 0 <= rr < n and 0 <= cc < n:
                    m[rr][cc] = 1 if ((0 <= dr <= 6 and dc in (0, 6))
                                      or (0 <= dc <= 6 and dr in (0, 6))
                                      or (2 <= dr <= 4 and 2 <= dc <= 4)) else 0

    finder(0, 0)
    finder(0, n - 7)
    finder(n - 7, 0)
    for i in range(8, n - 8):
        m[6][i] = m[i][6] = 1 - i % 2
    for r in ALIGN[version]:
        for c in ALIGN[version]:
            if (r < 9 and c < 9) or (r < 9 and c > n - 10) or (r > n - 10 and c < 9):
                continue
            for dr in range(-2, 3):
                for dc in range(-2, 3):
                    m[r + dr][c + dc] = 1 if max(abs(dr), abs(dc)) != 1 else 0
    if version >= 7:
        v = VERSION_BITS[version]
        for i in range(18):
            bit = (v >> i) & 1
            m[i // 3][n - 11 + i % 3] = bit
            m[n - 11 + i % 3][i // 3] = bit
    return m, n


def _reserved(version, n):
    res = [[False] * n for _ in range(n)]

    def block(r0, c0, h, w):
        for r in range(r0, r0 + h):
            for c in range(c0, c0 + w):
                if 0 <= r < n and 0 <= c < n:
                    res[r][c] = True

    block(0, 0, 9, 9)
    block(0, n - 8, 9, 8)
    block(n - 8, 0, 8, 9)
    for i in range(n):
        res[6][i] = res[i][6] = True
    for r in ALIGN[version]:
        for c in ALIGN[version]:
            if (r < 9 and c < 9) or (r < 9 and c > n - 10) or (r > n - 10 and c < 9):
                continue
            block(r - 2, c - 2, 5, 5)
    if version >= 7:
        block(0, n - 11, 6, 3)
        block(n - 11, 0, 3, 6)
    return res


_MASKS = [lambda i, j: (i + j) % 2 == 0, lambda i, j: i % 2 == 0,
          lambda i, j: j % 3 == 0, lambda i, j: (i + j) % 3 == 0,
          lambda i, j: (i // 2 + j // 3) % 2 == 0,
          lambda i, j: (i * j) % 2 + (i * j) % 3 == 0,
          lambda i, j: ((i * j) % 2 + (i * j) % 3) % 2 == 0,
          lambda i, j: ((i + j) % 2 + (i * j) % 3) % 2 == 0]


def _format_bits(mask):
    v = mask                                   # ECC level M = 00
    d = v << 10
    for i in range(4, -1, -1):
        if d & (1 << (i + 10)):
            d ^= 0b10100110111 << i
    return ((v << 10) | d) ^ 0b101010000010010


def _place_format(m, n, mask):
    f = _format_bits(mask)
    for i in range(15):
        bit = (f >> i) & 1
        if i < 6:
            m[i][8] = bit
        elif i < 8:
            m[i + 1][8] = bit
        else:
            m[n - 15 + i][8] = bit
        if i < 8:
            m[8][n - 1 - i] = bit
        elif i < 9:
            m[8][15 - i] = bit
        else:
            m[8][14 - i] = bit
    m[n - 8][8] = 1


def _penalty(m, n):
    score = 0
    for line in list(m) + [[m[r][c] for r in range(n)] for c in range(n)]:
        run, prev = 0, None
        for v in line:
            run = run + 1 if v == prev else 1
            if v != prev:
                prev = v
            if run == 5:
                score += 3
            elif run > 5:
                score += 1
    for r in range(n - 1):
        for c in range(n - 1):
            if m[r][c] == m[r][c + 1] == m[r + 1][c] == m[r + 1][c + 1]:
                score += 3
    pat = [1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0]
    for r in range(n):
        row, col = m[r], [m[k][r] for k in range(n)]
        for line in (row, col):
            for c in range(n - 10):
                if line[c:c + 11] in (pat, pat[::-1]):
                    score += 40
    dark = sum(sum(r) for r in m)
    return score + abs(dark * 100 // (n * n) - 50) // 5 * 10


def qr_matrix(text):
    data = text.encode("utf-8")
    version = next((v for v in range(1, 11)
                    if len(data) + 2 + (1 if v >= 10 else 0) <= SPEC[v][0]), None)
    if version is None:
        raise ValueError("too long for this encoder")
    stream = _interleave(_cw(data, version), version)
    base, n = _template(version)
    res = _reserved(version, n)
    bits = [(cw >> k) & 1 for cw in stream for k in range(7, -1, -1)]
    best, best_score = None, None
    for mask in range(8):
        m = [row[:] for row in base]
        fn, at, up, col = _MASKS[mask], 0, True, n - 1
        while col > 0:
            if col == 6:
                col -= 1
            for r in (range(n - 1, -1, -1) if up else range(n)):
                for c in (col, col - 1):
                    if res[r][c]:
                        continue
                    b = bits[at] if at < len(bits) else 0
                    at += 1
                    m[r][c] = b ^ (1 if fn(r, c) else 0)
            up = not up
            col -= 2
        _place_format(m, n, mask)
        s = _penalty(m, n)
        if best_score is None or s < best_score:
            best, best_score = m, s
    return best


def qr_svg(text, quiet=3):
    m = qr_matrix(text)
    n = len(m)
    total = n + quiet * 2
    parts = []
    for y, row in enumerate(m):
        x = 0
        while x < n:
            if row[x]:
                run = x
                while run < n and row[run]:
                    run += 1
                parts.append('<rect x="%d" y="%d" width="%d" height="1"/>'
                             % (x + quiet, y + quiet, run - x))
                x = run
            else:
                x += 1
    return ('<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 %d %d" '
            'shape-rendering="crispEdges"><rect width="%d" height="%d" fill="#fff"/>'
            '<g fill="#12181f">%s</g></svg>' % (total, total, total, total, "".join(parts)))


def qr_ascii(text):
    m = qr_matrix(text)
    n = len(m)
    pad = [0] * (n + 8)
    grid = [pad, pad] + [[0] * 4 + r + [0] * 4 for r in m] + [pad, pad]
    out = []
    for y in range(0, len(grid), 2):
        line = ""
        for x in range(len(grid[0])):
            top = grid[y][x]
            bot = grid[y + 1][x] if y + 1 < len(grid) else 0
            line += "█" if top and bot else "▀" if top else "▄" if bot else " "
        out.append("  " + line)
    return "\n".join(out)


# ══════════════════════════════════════════════════════════════════════
# the room
# ══════════════════════════════════════════════════════════════════════
HOTSPOT_HELP = """
Campus wifi often isolates clients: phones reach the internet but not this
laptop. If the QR opens a page that never loads, that is what happened.

Windows 11 : Settings -> Network & internet -> Mobile hotspot -> On,
             then re-run this script; the printed URL changes to the
             hotspot address and the QR is regenerated.
macOS      : System Settings -> General -> Sharing -> Internet Sharing.
Phone       : turn on the professor's personal hotspot, connect this laptop to
             it, have the students join the same hotspot. No uplink needed —
             the poll is entirely local.
"""

DEFAULT_POLLS = [{
    "id": "which-product",
    "q": "Which product do you want to be?",
    "options": ["Primary Product — core engineering roles",
                "Valuable by-Product — adjacent roles",
                "Fuel — roles far from the process",
                "Purge — thinking of leaving",
                "Still working it out"],
}]


def lan_addresses():
    found = []
    try:
        for info in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
            ip = info[4][0]
            if not ip.startswith("127.") and ip not in found:
                found.append(ip)
    except OSError:
        pass
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        if ip in found:
            found.remove(ip)
        found.insert(0, ip)
    except OSError:
        pass
    return found or ["127.0.0.1"]


def label_for(ip):
    if ip.startswith("192.168.137.") or ip.startswith("172.20.10."):
        return "hotspot"
    return "LAN / wifi" if ip.startswith(("192.168.", "10.", "172.")) else "other"


class State:
    """Counts and questions plus a version, so SSE clients only get changes."""

    def __init__(self, polls, room, path):
        self.polls = polls
        self.room = room
        self.counts = {p["id"]: [0] * len(p["options"]) for p in polls}
        self.voters = {p["id"]: {} for p in polls}
        self.questions = []
        self.version = 0
        self.path = path
        self.lock = threading.Lock()

    def vote(self, pid, index, token):
        with self.lock:
            if pid not in self.counts or not (0 <= index < len(self.counts[pid])):
                return False
            prev = self.voters[pid].get(token)
            if prev == index:
                return True
            if prev is not None:
                self.counts[pid][prev] -= 1     # one device, one vote — changing
            self.counts[pid][index] += 1        # your mind moves it, not adds
            self.voters[pid][token] = index
            self.version += 1
            self._save()
            return True

    def ask(self, text, token):
        text = " ".join(str(text).split())[:180]
        if not text:
            return False
        with self.lock:
            self.questions.insert(0, {"text": text,
                                      "at": time.strftime("%H:%M"),
                                      "who": str(token)[:12]})
            del self.questions[200:]
            self.version += 1
            self._save()
            return True

    def reset(self, pid):
        with self.lock:
            if pid in self.counts:
                self.counts[pid] = [0] * len(self.counts[pid])
                self.voters[pid] = {}
                self.version += 1
                self._save()

    def clear_questions(self):
        with self.lock:
            self.questions = []
            self.version += 1
            self._save()

    def snapshot(self):
        with self.lock:
            return {"version": self.version,
                    "counts": {k: list(v) for k, v in self.counts.items()},
                    "totals": {k: sum(v) for k, v in self.counts.items()},
                    "questions": [dict(q) for q in self.questions]}

    def _save(self):
        try:
            self.path.write_text(json.dumps(
                {"savedAt": time.strftime("%Y-%m-%d %H:%M:%S"), "room": self.room,
                 "polls": self.polls, "counts": self.counts,
                 "questions": self.questions}, ensure_ascii=False, indent=2), "utf-8")
        except OSError:
            pass


PHONE_PAGE = """<!DOCTYPE html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<title>Orientation 2569 — live</title><style>
:root{--ink:#12181f;--ink2:#5a656f;--line:#e3e7ea;--brand:#c00000;--good:#1a8a5a;
 --goodbg:#e6f4ee;--soft:#f5f7f8;
 --font:"Montserrat","Prompt","Segoe UI",system-ui,-apple-system,sans-serif}
*{box-sizing:border-box;margin:0;padding:0;-webkit-tap-highlight-color:transparent}
body{font-family:var(--font);background:#fff;color:var(--ink);line-height:1.5;
 padding:max(16px,env(safe-area-inset-top)) 16px 46px}
.wrap{max-width:560px;margin:0 auto}
h1{font-size:23px;font-weight:800}
.room{display:inline-block;margin:6px 0 2px;font-size:14px;color:var(--ink2)}
.room b{font-size:17px;letter-spacing:.06em;color:var(--ink)}
.sub{font-size:15px;color:var(--ink2);margin-bottom:18px}
.q{font-size:20px;font-weight:700;margin:22px 0 10px}
button.opt{display:block;width:100%;text-align:left;font:600 19px/1.35 var(--font);
 padding:16px 18px;margin-bottom:10px;border:2px solid var(--line);border-radius:16px;
 background:#fff;color:var(--ink)}
button.opt:active{transform:scale(.985)}
button.opt.picked{border-color:var(--good);background:var(--goodbg);color:var(--good)}
.tally{font-size:14px;color:var(--ink2);margin:-2px 0 6px}
.card{border:1px solid var(--line);border-radius:16px;padding:16px;margin-top:26px;
 background:var(--soft)}
.card h2{font-size:19px;font-weight:800;margin-bottom:8px}
textarea{width:100%;font:400 18px/1.4 var(--font);padding:12px 14px;border-radius:14px;
 border:1px solid var(--line);resize:vertical;min-height:92px;color:var(--ink)}
.send{margin-top:10px;width:100%;font:700 19px var(--font);padding:14px;border:0;
 border-radius:14px;background:var(--brand);color:#fff}
.mine{margin-top:12px;font-size:15px;color:var(--ink2)}
.mine div{padding:8px 0;border-top:1px solid var(--line)}
.msg{display:none;font-size:15px;border-radius:12px;padding:11px 14px;margin-top:12px}
.msg.ok{display:block;background:var(--goodbg);color:var(--good)}
.msg.bad{display:block;background:#fbeaea;color:var(--brand)}
.foot{margin-top:30px;padding-top:16px;border-top:1px solid var(--line);
 font-size:13px;color:var(--ink2)}
</style></head><body><div class="wrap">
<h1>Orientation 2569 — live</h1>
<p class="room">room code <b>__ROOM__</b></p>
<p class="sub">Tap an answer, or send a question. Both appear on the screen at the front
straight away. Changed your mind? Tap another answer.</p>
<div id="qs"></div>
<div class="card"><h2>Ask a question</h2>
  <textarea id="qa" maxlength="180" placeholder="Anything about the curriculum, the courses, the four years…"></textarea>
  <button class="send" id="qasend" type="button">Send to the screen</button>
  <div class="mine" id="mine"></div>
</div>
<div class="msg" id="msg"></div>
<p class="foot">Department of Chemical Engineering, Faculty of Engineering,
Chulalongkorn University</p>
</div><script>
const Q = __POLLS__, ROOM = "__ROOM__";
const token = 'd' + Math.random().toString(36).slice(2) + Date.now().toString(36);
const msg = document.getElementById('msg'), host = document.getElementById('qs');
const btns = {};
function say(text, ok){ msg.textContent = text; msg.className = 'msg ' + (ok ? 'ok' : 'bad');
  clearTimeout(say.t); say.t = setTimeout(() => msg.className = 'msg', 2600); }
Q.forEach(p => {
  const h = document.createElement('div'); h.className = 'q'; h.textContent = p.q;
  host.appendChild(h);
  const t = document.createElement('div'); t.className = 'tally'; t.id = 't_' + p.id;
  host.appendChild(t);
  btns[p.id] = p.options.map((label, i) => {
    const b = document.createElement('button'); b.className = 'opt'; b.type = 'button';
    b.textContent = label; b.onclick = () => vote(p.id, i, b); host.appendChild(b); return b;
  });
});
async function vote(pid, i, b){
  try{
    const r = await fetch('/api/vote', {method:'POST',
      headers:{'Content-Type':'application/json'},
      body: JSON.stringify({poll:pid, option:i, token, room:ROOM})});
    if(!r.ok) throw 0;
    btns[pid].forEach(x => x.classList.remove('picked')); b.classList.add('picked');
    say('Counted', true);
  }catch(e){ say('Could not send — are you still on the same wifi?', false); }
}
document.getElementById('qasend').onclick = async () => {
  const box = document.getElementById('qa'), text = box.value.trim();
  if(!text) return;
  try{
    const r = await fetch('/api/ask', {method:'POST',
      headers:{'Content-Type':'application/json'},
      body: JSON.stringify({text, token, room:ROOM})});
    if(!r.ok) throw 0;
    box.value = '';
    const d = document.createElement('div'); d.textContent = text;
    document.getElementById('mine').prepend(d);
    say('It is on the screen', true);
  }catch(e){ say('Could not send — are you still on the same wifi?', false); }
};
const es = new EventSource('/api/stream');
es.onmessage = e => { const d = JSON.parse(e.data);
  Q.forEach(p => { const el = document.getElementById('t_' + p.id); const n = d.totals[p.id] || 0;
    if(el) el.textContent = n + (n === 1 ? ' response so far' : ' responses so far'); }); };
</script></body></html>"""


def make_handler(state, deck_path, join_url):
    polls_json = json.dumps(state.polls, ensure_ascii=False)
    qr = qr_svg(join_url)

    class H(BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.1"

        def log_message(self, fmt, *a):
            pass

        def _send(self, code, body=b"", ctype="text/plain; charset=utf-8"):
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Access-Control-Allow-Origin", "*")
            self.send_header("Access-Control-Allow-Headers", "Content-Type")
            self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
            self.end_headers()
            if body:
                self.wfile.write(body)

        def do_OPTIONS(self):
            self._send(204)

        def do_GET(self):
            path = self.path.split("?")[0]
            if path in ("/", "/vote", "/index.html"):
                page = (PHONE_PAGE.replace("__POLLS__", polls_json)
                                  .replace("__ROOM__", state.room))
                return self._send(200, page.encode("utf-8"), "text/html; charset=utf-8")
            if path == "/api/info":
                return self._send(200, json.dumps(
                    {"room": state.room, "join": join_url, "qr": qr},
                    ensure_ascii=False).encode(), "application/json")
            if path == "/api/qr":
                return self._send(200, qr.encode(), "image/svg+xml")
            if path == "/api/results":
                return self._send(200, json.dumps(state.snapshot(),
                                                  ensure_ascii=False).encode(),
                                  "application/json")
            if path == "/api/stream":
                return self._stream()
            if path == "/deck" and deck_path and deck_path.is_file():
                return self._send(200, deck_path.read_bytes(),
                                  "text/html; charset=utf-8")
            return self._send(404, b"not found")

        def _stream(self):
            self.send_response(200)
            self.send_header("Content-Type", "text/event-stream; charset=utf-8")
            self.send_header("Cache-Control", "no-cache")
            self.send_header("Connection", "keep-alive")
            self.send_header("Access-Control-Allow-Origin", "*")
            self.end_headers()
            last = -1
            try:
                while True:
                    snap = state.snapshot()
                    if snap["version"] != last:
                        last = snap["version"]
                        self.wfile.write(("data: %s\n\n" % json.dumps(
                            snap, ensure_ascii=False)).encode("utf-8"))
                    else:
                        self.wfile.write(b": keepalive\n\n")
                    self.wfile.flush()
                    time.sleep(0.6)
            except (BrokenPipeError, ConnectionResetError):
                return

        def do_POST(self):
            path = self.path.split("?")[0]
            n = int(self.headers.get("Content-Length") or 0)
            try:
                body = json.loads(self.rfile.read(n) or b"{}")
            except json.JSONDecodeError:
                return self._send(400, b"bad json")
            room = str(body.get("room", state.room)).strip().upper()
            if path in ("/api/vote", "/api/ask") and room != state.room:
                return self._send(403, json.dumps(
                    {"ok": False, "error": "wrong room code"}).encode(),
                    "application/json")
            if path == "/api/vote":
                ok = state.vote(body.get("poll"), int(body.get("option", -1)),
                                body.get("token", self.client_address[0]))
            elif path == "/api/ask":
                ok = state.ask(body.get("text", ""),
                               body.get("token", self.client_address[0]))
            elif path == "/api/reset":
                state.reset(body.get("poll"))
                ok = True
            elif path == "/api/qa/clear":
                state.clear_questions()
                ok = True
            else:
                return self._send(404, b"not found")
            return self._send(200 if ok else 400,
                              json.dumps({"ok": ok}).encode(), "application/json")

    return H


def wire_deck(deck: pathlib.Path, url: str, room: str):
    """Point a built deck at this server by rewriting its POLL_CONFIG block."""
    src = deck.read_text("utf-8")
    new, n = re.subn(r'(const\s+POLL_CONFIG\s*=\s*)\{.*?\}',
                     lambda m: m.group(1) + ('{\n  url:     "%s",\n  room:    "%s",\n'
                                             '  voteUrl: "%s"\n}' % (url, room, url)),
                     src, count=1, flags=re.S)
    if n:
        deck.write_text(new, "utf-8")
    return bool(n)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("polls", nargs="?", help="polls.json (optional — one is built in)")
    ap.add_argument("--port", type=int, default=8080)
    ap.add_argument("--room", default="")
    ap.add_argument("--deck", help="deck .html — wired to this server and served at /deck")
    ap.add_argument("--results", default="live-results.json")
    ap.add_argument("--hotspot-help", action="store_true")
    a = ap.parse_args()

    if a.hotspot_help:
        print(HOTSPOT_HELP)
        return 0

    polls = (json.loads(pathlib.Path(a.polls).read_text("utf-8"))
             if a.polls else DEFAULT_POLLS)
    room = (a.room or ("CHE" + "".join(random.choice(string.digits) for _ in range(2))
                       + random.choice("ABCDEFGHJKLMNPQRSTUVWXYZ"))).upper()
    state = State(polls, room, pathlib.Path(a.results))

    ips = lan_addresses()
    join = "http://%s:%d/?r=%s" % (ips[0], a.port, room)
    deck = pathlib.Path(a.deck) if a.deck else None
    if deck and deck.is_file():
        ok = wire_deck(deck, "http://%s:%d" % (ips[0], a.port), room)
        print("%s deck %s %s" % ("✓" if ok else "!",
                                 "wired to this server:" if ok else
                                 "has no POLL_CONFIG block:", deck.name))

    srv = ThreadingHTTPServer(("0.0.0.0", a.port), make_handler(state, deck, join))
    srv.daemon_threads = True

    print("\n" + "=" * 62)
    print("  Live poll and Q&A are up — have the students scan this")
    print("=" * 62)
    print(qr_ascii(join))
    print("\n  %s" % join)
    print("  room code: %s" % room)
    if len(ips) > 1:
        print("\n  Other addresses of this laptop (pick the network the students joined):")
        for ip in ips[1:]:
            print("    http://%s:%d/?r=%s   [%s]" % (ip, a.port, room, label_for(ip)))
    if deck:
        print("\n  Open the deck at  http://localhost:%d/deck" % a.port)
        print("  (or just open the .html file — it was wired to this server above)")
    print("  Votes and questions are saved continuously to  %s" % a.results)
    print("\n  Phones cannot open the page? Campus wifi is isolating clients —")
    print("  python3 %s --hotspot-help" % pathlib.Path(__file__).name)
    print("  Ctrl-C to stop\n")

    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("\nStopped — everything is in", a.results)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
