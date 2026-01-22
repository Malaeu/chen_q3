# Platform Router — Q3 Sandbox

Use the OS-specific memory file:
- `./CLAUDE_linux.md` (Linux)
- `./CLAUDE_mac.md` (macOS)

Quick detect:
```bash
uname -s
# Linux  -> CLAUDE_linux.md
# Darwin -> CLAUDE_mac.md
```

If you want a one-liner:
```bash
case "$(uname -s)" in
  Darwin) ${PAGER:-less} ./CLAUDE_mac.md ;;
  Linux)  ${PAGER:-less} ./CLAUDE_linux.md ;;
  *) echo "Unknown OS. Open the right file manually." ;;
esac
```
