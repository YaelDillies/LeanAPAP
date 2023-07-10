const commit = [["https://github.com/leanprover-community/mathlib/blob/master/src/", "https://github.com/leanprover-community/mathlib/blob/5d0c76894ada7940957143163d7b921345474cbc/src/"], ["https://github.com/leanprover-community/mathlib/blob/master/archive/", "https://github.com/leanprover-community/mathlib/blob/5d0c76894ada7940957143163d7b921345474cbc/archive/"], ["https://github.com/leanprover-community/mathlib/blob/master/counterexamples/", "https://github.com/leanprover-community/mathlib/blob/5d0c76894ada7940957143163d7b921345474cbc/counterexamples/"]];
function redirectTo(tgt) {
  let loc = tgt;
  for (const [prefix, replacement] of commit) {
    if (tgt.startsWith(prefix)) {
      loc = tgt.replace(prefix, replacement);
      break;
    }
  }
  window.location.replace(loc);
}
