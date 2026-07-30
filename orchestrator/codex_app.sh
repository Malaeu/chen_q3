#!/bin/bash
# Codex.app lane — drive the desktop Codex through its GUI.
#
# Why: Codex.app carries an embedded browser already logged into the owner's
# Aristotle account, so work routed through it needs no API key. The CLI lane
# (codex exec) stays available and is easier to read; this lane is for work that
# must go through the app itself.
#
# THE TWO THINGS THAT COST US AN HOUR
#
# 1. Permission is handed out at process start.
#    Ticking Accessibility for a running Ghostty does nothing -- it keeps the
#    answer it got when it launched. Quit and relaunch the app, not the shell.
#    Closing the permission dialog counts as a permanent DENY; clear it with
#      tccutil reset Accessibility com.mitchellh.ghostty
#
# 2. cliclick/keystroke synthesise KEY PRESSES, not text.
#    They say "press the key at position 17", and the active layout decides what
#    that becomes. Cyrillic has no key in a Latin layout, so nothing is typed --
#    silently. Everything non-ASCII goes through the clipboard instead, which
#    carries the text itself and bypasses the layout entirely.
#
# READ BEFORE YOU WRITE. The composer keeps whatever was left in it, including
# garbage from failed keystroke attempts. Typing without looking appends to
# invisible leftovers and then the result looks "broken" for no reason.
#
# Prerequisites (done 2026-07-30): Accessibility granted to Ghostty AND Ghostty
# relaunched; brew install cliclick.
#
# Usage:
#   ./codex_app.sh probe          # geometry, composer point, permission check
#   ./codex_app.sh read           # what is in the composer right now
#   ./codex_app.sh write "text"   # replace the composer contents, do NOT send
#   ./codex_app.sh send "text"    # replace, verify, then press Enter
#   ./codex_app.sh file <path>    # same as write, from a file

set -uo pipefail

BUNDLE="ChatGPT"

geometry() {
  osascript -l JavaScript -e '
    const se = Application("System Events");
    const w = se.processes["ChatGPT"].windows()[0];
    JSON.stringify({ pos: w.position(), size: w.size() });
  ' 2>/dev/null
}

# Derived from the window box, not hard-coded: a resize would otherwise start
# clicking silently into the wrong pane.
composer_point() {
  geometry | python3 -c '
import json, sys
g = json.load(sys.stdin)
x0, y0 = g["pos"]
w, h = g["size"]
print(f"{int(x0 + w * 0.45)},{int(y0 + h * 0.92)}")
'
}

focus_composer() {
  osascript -e "tell application \"$BUNDLE\" to activate" >/dev/null 2>&1
  sleep 1
  cliclick "c:$(composer_point)" >/dev/null 2>&1
  sleep 0.5
}

# Read by round-tripping through the clipboard: plant a marker, select-all and
# copy, then see whether the marker survived. AX gives no usable value here --
# JXA cannot even return focusedUIElement for this Electron window.
read_composer() {
  local mark="__COMPOSER_EMPTY_$$__"
  printf '%s' "$mark" | pbcopy
  cliclick kd:cmd t:a ku:cmd >/dev/null 2>&1
  sleep 0.4
  cliclick kd:cmd t:c ku:cmd >/dev/null 2>&1
  sleep 0.6
  local got
  got=$(pbpaste)
  [ "$got" = "$mark" ] && echo "" || printf '%s' "$got"
}

# Select-all then paste: the paste replaces the selection. Cmd+A followed by
# Delete does NOT clear this composer -- the text highlights and stays.
write_composer() {
  printf '%s' "$1" | pbcopy
  cliclick kd:cmd t:a ku:cmd >/dev/null 2>&1
  sleep 0.4
  cliclick kd:cmd t:v ku:cmd >/dev/null 2>&1
  sleep 0.6
}

case "${1:-}" in
  probe)
    echo "window:  $(geometry)"
    echo "composer: $(composer_point)"
    command -v cliclick >/dev/null && echo "cliclick: $(cliclick -V | head -1)" || echo "cliclick: MISSING"
    osascript -l JavaScript -e '
      const se = Application("System Events");
      try { se.processes["ChatGPT"].windows().length; "a11y:    ok"; }
      catch (e) { "a11y:    DENIED -- " + e.message; }
    ' 2>&1
    ;;

  read)
    focus_composer
    got=$(read_composer)
    if [ -z "$got" ]; then
      echo "composer is EMPTY"
    else
      echo "composer holds ${#got} chars:"
      printf '%s\n' "$got"
    fi
    ;;

  write|send)
    text="${2:-}"
    [ -z "$text" ] && { echo "usage: $0 $1 \"text\""; exit 1; }
    focus_composer

    before=$(read_composer)
    [ -n "$before" ] && echo "note: overwriting ${#before} existing chars"

    write_composer "$text"

    after=$(read_composer)
    if [ "$after" != "$text" ]; then
      echo "VERIFY FAILED -- composer holds ${#after} chars, expected ${#text}"
      printf 'got: %s\n' "$after"
      exit 1
    fi
    echo "verified: composer holds exactly the ${#text} chars requested"

    if [ "$1" = "send" ]; then
      # read_composer left everything selected; click once to drop the
      # selection, or Enter would replace rather than submit.
      cliclick "c:$(composer_point)" >/dev/null 2>&1
      sleep 0.3
      cliclick kp:return >/dev/null 2>&1
      echo "sent"
    else
      echo "NOT sent"
    fi
    ;;

  file)
    path="${2:-}"
    [ -f "$path" ] || { echo "no such file: $path"; exit 1; }
    exec "$0" write "$(cat "$path")"
    ;;

  *)
    echo "usage: $0 {probe|read|write|send|file} [arg]"
    exit 1
    ;;
esac
