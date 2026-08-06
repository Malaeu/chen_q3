A=q3.lean.aristotle
RB=$A/ACTIVE/requests/routeB_twolevel_spectral_ladder
docs="AGENTS.md docs/CODEX_CONTROL.md SESSION_ENTRY.md $A/PROJECT_ORCHESTRATOR.md IMPLEMENTATION_PLAN.md $A/docs/PAPER_MAINLINE_TRACKER.md $A/docs/INSIGHTS.md orchestrator/state/SPINE_VIEW.md orchestrator/state/CHANNEL_RUNTIME.json $RB/ROUTE_B_EXECUTION_STATE.json $RB/ROUTE_B_EXECUTION_CONTROL.md $RB/ROUTE_B_STATE.md $RB/bus/BUS_PROTOCOL.md $A/ACTIVE/PSD_STEP33_MONITOR.md $A/ACTIVE/requests/step33_bootstrap/node.md $A/ACTIVE/requests/step33_bootstrap/report.md $A/ACTIVE/PHASE_MONITOR.md $A/ACTIVE/SPRINT_MONITOR.md $A/COGNITIVE_KERNEL.md $A/COGNITIVE_OPERATORS.md $A/ACTIVE/COGNITIVE_GOVERNOR.md $A/docs/EMBEDDING_INGEST_WORKFLOW.md $A/ACTIVE/pipeline/RESEARCH_ORACLE.md $A/ACTIVE/pipeline/oracle_questions/INDEX.md $A/ACTIVE/pipeline/oracle_questions/BY_ADDRESS.md $A/ACTIVE/aristotle/ARISTOTLE_WORKFLOW.md $A/aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md"
printf "%-52s %-11s %-7s %-4s %s\n" "ДОКУМЕНТ" "ПОСЛЕДНИЙ" "КОММИТ" "30д" "ТИП"
printf "%.0s─" {1..104}; echo
for f in $docs; do
  if [ ! -e "$f" ]; then printf "%-52s %s\n" "$(echo $f|rev|cut -c1-52|rev)" "✗ НЕТ"; continue; fi
  last=$(git log -1 --format=%ad --date=short -- "$f" 2>/dev/null); last=${last:-untracked}
  who=$(git log -1 --format=%s -- "$f" 2>/dev/null | grep -o '\[MacOS\]\|\[Linux\]' | head -1); who=${who:-—}
  n=$(git log --since='30 days ago' --oneline -- "$f" 2>/dev/null | wc -l)
  gen="ручной"
  head -8 "$f" 2>/dev/null | grep -qi "GENERATED\|DO NOT EDIT\|auto-generated\|regenerate" && gen="ГЕНЕРИРУЕТСЯ"
  printf "%-52s %-11s %-7s %-4s %s\n" "$(echo $f|rev|cut -c1-52|rev)" "$last" "$who" "$n" "$gen"
done
