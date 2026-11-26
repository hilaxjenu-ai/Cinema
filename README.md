# Hilax Cinema Web App

Ready-to-upload repository package for GitHub (`https://hilax.vinokaran.my.id:5000/`).

## Files Included
- `app.py` — Flask backend and proxy endpoints
- `templates/index.html` — Mobile Netflix-style frontend UI
- `requirements.txt` — Python dependencies
- `.gitignore` — Clean Git ignore rules

## GitHub Upload & Run
```bash
git init
git add .
git commit -m "Add Hilax Cinema web app"
git branch -M main
git remote add origin <YOUR_GITHUB_REPO_URL>
git push -u origin main
```

On the server:
```bash
pip install -r requirements.txt
python app.py
```
