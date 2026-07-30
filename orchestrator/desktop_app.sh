#!/bin/bash
# Desktop lane — drive Codex.app and Claude Desktop through their GUI.
#
# Owner's decision 2026-07-30: the browser is kept for Proshka only. Codex and
# Mythos are driven as desktop apps; Aristotle goes through the CLI. Codex.app
# additionally carries an embedded browser already signed into the owner's
# Aristotle, and the owner can watch the work happen on screen.
#
# THE THINGS THAT COST US AN HOUR
#
# 1. Permission is handed out at process start.
#    Ticking Accessibility for a running Ghostty does nothing -- it keeps the
#    answer it got at launch. Quit and relaunch the app, not the shell.
#    Dismissing the permission dialog records a permanent DENY; clear it with
#      tccutil reset Accessibility com.mitchellh.ghostty
#
# 2. cliclick and keystroke synthesise KEY PRESSES, not text.
#    The active layout decides what a key becomes. Cyrillic has no key in a
#    Latin layout, so it types nothing at all -- silently. Everything non-ASCII
#    goes through the clipboard, which carries the text itself.
#
# 3. Cmd+A then Delete does NOT clear these composers; the text highlights and
#    stays. Pasting over the selection does clear it.
#
# 4. Claude Desktop and claude.ai share the composer draft. Text left in one
#    surfaces in the other -- so a composer can hold an already-sent message,
#    or one the owner is still writing.
#
# READ BEFORE YOU WRITE, ALWAYS. Owner's rule: understand what is already in
# the composer, do not merely verify what you wrote. A leftover may be the
# owner's half-typed prompt. Unsure means hands off.
#
# Usage:
#   ./desktop_app.sh <app> probe          # geometry, composer point, permission
#   ./desktop_app.sh <app> read           # what is in the composer now
#   ./desktop_app.sh <app> write "text"   # replace contents, do NOT send
#   ./desktop_app.sh <app> send "text"    # replace, verify, then Enter
#   ./desktop_app.sh <app> file <path>    # write, from a file
#
#   <app> is: codex | claude

set -uo pipefail

APP="${1:-}"
shift || true

case "$APP" in
  codex)
    PROC="ChatGPT"
    # Codex.app keeps an embedded browser on the right, so the composer sits
    # left of centre.
    XFRAC=0.45
    ;;
  claude)
    PROC="Claude"
    # Claude Desktop has no right pane; the composer is centred in the main
    # column, right of the sidebar.
    XFRAC=0.55
    ;;
  *)
    echo "usage: $0 {codex|claude} {probe|read|write|send|file} [arg]"
    exit 1
    ;;
esac

YFRAC=0.92

geometry() {
  osascript -l JavaScript -e "
    const se = Application('System Events');
    const w = se.processes['$PROC'].windows()[0];
    JSON.stringify({ pos: w.position(), size: w.size() });
  " 2>/dev/null
}

# Derived from the window box, not hard-coded: a resize would otherwise start
# clicking silently into the wrong pane.
composer_point() {
  geometry | tr -d '{}"' | tr ',:[]' ' ' | awk -v xf="$XFRAC" -v yf="$YFRAC" '
    { for (i = 1; i <= NF; i++) {
        if ($i == "pos")  { x0 = $(i+1); y0 = $(i+2) }
        if ($i == "size") { w  = $(i+1); h  = $(i+2) }
      }
      printf "%d,%d\n", x0 + w * xf, y0 + h * yf }'
}

focus_composer() {
  osascript -e "tell application \"$PROC\" to activate" >/dev/null 2>&1
  sleep 1
  cliclick "c:$(composer_point)" >/dev/null 2>&1
  sleep 0.5
}

# Read by round-tripping through the clipboard: plant a marker, select-all and
# copy, then see whether the marker survived. AX gives nothing usable here --
# JXA cannot even return focusedUIElement for these Electron windows.
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

write_composer() {
  printf '%s' "$1" | pbcopy
  cliclick kd:cmd t:a ku:cmd >/dev/null 2>&1
  sleep 0.4
  cliclick kd:cmd t:v ku:cmd >/dev/null 2>&1
  sleep 0.6
}

ACTION="${1:-}"
shift || true

case "$ACTION" in
  probe)
    echo "app:      $APP ($PROC)"
    echo "window:   $(geometry)"
    echo "composer: $(composer_point)"
    command -v cliclick >/dev/null && echo "cliclick: $(cliclick -V | head -1)" || echo "cliclick: MISSING"
    osascript -l JavaScript -e "
      const se = Application('System Events');
      try { se.processes['$PROC'].windows().length; 'a11y:     ok'; }
      catch (e) { 'a11y:     DENIED -- ' + e.message; }
    " 2>&1
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
    text="${1:-}"
    [ -z "$text" ] && { echo "usage: $0 $APP $ACTION \"text\""; exit 1; }
    focus_composer

    before=$(read_composer)
    [ -n "$before" ] && echo "note: overwriting ${#before} existing chars"

    write_composer "$text"

    after=$(read_composer)
    if [ "$after" != "$text" ]; then
      echo "VERIFY FAILED -- composer holds ${#after} chars, expected ${#text}"
      exit 1
    fi
    echo "verified: composer holds exactly the ${#text} chars requested"

    if [ "$ACTION" = "send" ]; then
      # read_composer left everything selected; click once to drop the
      # selection, or Enter would replace it rather than submit.
      cliclick "c:$(composer_point)" >/dev/null 2>&1
      sleep 0.3
      cliclick kp:return >/dev/null 2>&1
      echo "sent"
    else
      echo "NOT sent"
    fi
    ;;

  file)
    path="${1:-}"
    [ -f "$path" ] || { echo "no such file: $path"; exit 1; }
    exec "$0" "$APP" write "$(cat "$path")"
    ;;

  *)
    echo "usage: $0 {codex|claude} {probe|read|write|send|file} [arg]"
    exit 1
    ;;
esac
