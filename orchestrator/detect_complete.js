// detect_complete.js — is the browser agent still generating?
// Single-signal buttons lie (e.g. a hidden "Stop response" stays in the DOM), so the
// robust rule combines: no streaming node + no "responding/thinking" indicator, AND the
// conductor calls this twice ~3s apart and confirms `lastLen` is stable.
//
// Use with chrome-devtools-mcp evaluate_script on the agent tab.
// Returns { generating, lastLen, host }. Conductor: done = (!generating) && lastLen equal
// across two consecutive polls.

() => {
  const host = location.host;
  const body = document.body.innerText || '';
  const streamingNodes = document.querySelectorAll('[class*="streaming" i], .result-streaming').length;
  const respondingText = /is responding|Claude is responding|Pro thinking|Thinking about|Оркеструя|Верифицируя|Конструир/i.test(body);
  // last assistant text length as a stability proxy (works without knowing selectors)
  const lastLen = body.length;
  const generating = streamingNodes > 0 || respondingText;
  return { generating, streamingNodes, respondingText, lastLen, host };
}
