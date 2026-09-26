---
title: 課堂點名系統
emoji: 📋
colorFrom: green
colorTo: blue
sdk: streamlit
sdk_version: "1.64.0"
app_file: app.py
pinned: false
---

# 課堂點名系統

Lesson Rolls Call System. The teacher starts a class on this computer. Students open the QR link on their own phones, match `student_email` and `student_number` to the roster, and take a selfie.

`st.session_state` is not shared across phones. The roster, active lesson, attendance workbook, and selfie files are stored on disk under `data/`, and every session reads those files.

## Attendance rules

Check-in time is the Mac's local time, compared with `start_time` on `class_date`:

- check-in at or before the start: status `準時出席`, student email `你準時出席`
- after the start, up to 15 minutes: status `遲到`, student email `你已經遲到`
- later than 15 minutes: status `缺席`, student email `你已經缺席`

## Run locally

```bash
cd ~/Documents/Cursor_Rolls_Call_App
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
streamlit run app.py --server.address 0.0.0.0 --server.port 8765
```

Open `http://127.0.0.1:8765` on this Mac. In **設定**, put the LAN address shown on the teacher page into **公開網址** (for example `http://192.168.1.20:8765`). Phones cannot open `localhost`. The phone and this Mac need the same Wi-Fi.

Optional email: copy `.env.example` to `.env`, or copy `.streamlit/secrets.toml.example` to `.streamlit/secrets.toml`.

## Gmail app password

Gmail rejects the normal account password for SMTP. Turn on 2-Step Verification, then create an app password at Google Account → Security → App passwords. Use:

- `SMTP_HOST` = `smtp.gmail.com`
- `SMTP_PORT` = `587` (STARTTLS)
- `SMTP_USER` = the Gmail address
- `SMTP_PASSWORD` = the 16-character app password
- `SMTP_FROM` = the same Gmail address

If SMTP is missing or the send fails, attendance is still saved and the screen says the email was not sent.

## Hugging Face Spaces secrets

Space settings → Secrets, same keys as `.streamlit/secrets.toml.example`:

`SMTP_HOST`, `SMTP_PORT`, `SMTP_USER`, `SMTP_PASSWORD`, `SMTP_FROM`

The app reads `smtp.txt` first, then Streamlit secrets, then environment variables and `.env`. If `smtp.txt` and `.env` both set a key, `smtp.txt` wins. Do not commit real passwords. Spaces disk is ephemeral: `data/` can disappear when the Space restarts. This classroom copy is meant to run on the Mac.

## Check-in

There is no photo. After the roster match, the page asks for one GPS reading (`getCurrentPosition` only). If location is denied, check-in stops with `請開啟定位功能後再點名`. The attendance row stores latitude, longitude, accuracy, and a Google Maps link.

iPhone Safari will not share GPS on an `http://` Wi-Fi address. On a Hugging Face Space the teacher QR uses that Space’s own `https://….hf.space` URL. On this Mac it uses `data/https_origin.txt`. The code on the teacher page changes every 30 seconds; each token works once. Opening it again shows `此二維碼已失效，請重新掃描老師畫面上的二維碼`.

SMTP is optional; without it, check-in still writes `data/attendance.xlsx`.

## Data files

- `data/roster.csv` — uploaded roster
- `data/roster_template.csv` — sample columns
- `data/settings.json` — teacher email and public base URL
- `data/session.json` — active lesson
- `data/attendance.xlsx` — current lesson roll, including latitude and longitude
- `data/https_origin.txt` — HTTPS origin used by the teacher QR
- `data/qr_tokens.json` — rotating check-in tokens
