// harvest_conversation.js — reliable full-conversation harvest, bypassing DOM
// virtualization (claude.ai / ChatGPT only mount a window of messages, so DOM reads
// miss off-screen turns). Fetches the app's own conversation JSON, same-origin, with
// the logged-in session.
//
// Use with chrome-devtools-mcp evaluate_script:
//   select_page {pageId of the agent tab}
//   evaluate_script { function: "<paste the async function below>" }
// Returns { host, count, messages: [{sender, text}] }.

async () => {
  const host = location.host;

  // ---- claude.ai ----
  if (host.includes('claude.ai')) {
    // discover the conversation endpoint the app already called
    const perf = performance.getEntriesByType('resource').map(r => r.name);
    const id = location.pathname.split('/').pop();
    const cand = perf.filter(u => /chat_conversations\//.test(u));
    let base = cand.find(u => u.includes(id)) || cand[cand.length - 1];
    if (!base) {
      // fallback: build from org uuid if present in any api url
      const org = (perf.find(u => /organizations\/[0-9a-f-]{36}\//.test(u)) || '')
        .match(/organizations\/([0-9a-f-]{36})/);
      if (org) base = `/api/organizations/${org[1]}/chat_conversations/${id}`;
    }
    if (!base) return { host, error: 'no claude conversation endpoint found' };
    const url = base.split('?')[0] + '?tree=True&rendering_mode=messages';
    const j = await fetch(url, { credentials: 'include' }).then(r => r.json());
    const messages = (j.chat_messages || []).map(m => ({
      sender: m.sender, // 'human' | 'assistant'
      text: Array.isArray(m.content) ? m.content.map(c => c.text || '').join('') : (m.text || '')
    }));
    return { host, count: messages.length, messages };
  }

  // ---- chatgpt.com ----
  if (host.includes('chatgpt.com') || host.includes('chat.openai.com')) {
    const id = location.pathname.split('/').pop();
    // backend-api needs a bearer token from the session endpoint
    const sess = await fetch('/api/auth/session', { credentials: 'include' }).then(r => r.json());
    const tok = sess && sess.accessToken;
    if (!tok) return { host, error: 'no chatgpt accessToken' };
    const j = await fetch('/backend-api/conversation/' + id, {
      credentials: 'include',
      headers: { Authorization: 'Bearer ' + tok }
    }).then(r => r.json());
    // walk the mapping tree in order
    const map = j.mapping || {};
    const nodes = Object.values(map).filter(n => n.message && n.message.author);
    // order by create_time when available
    nodes.sort((a, b) => (a.message.create_time || 0) - (b.message.create_time || 0));
    const messages = nodes.map(n => {
      const role = n.message.author.role; // 'user' | 'assistant' | 'system' | 'tool'
      const parts = (n.message.content && n.message.content.parts) || [];
      const text = parts.map(p => (typeof p === 'string' ? p : (p && p.text) || '')).join('');
      return { sender: role, text };
    }).filter(m => m.sender === 'user' || m.sender === 'assistant');
    return { host, count: messages.length, messages };
  }

  return { host, error: 'unsupported host' };
}
