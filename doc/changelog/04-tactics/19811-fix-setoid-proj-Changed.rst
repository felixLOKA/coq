- **Changed:**
  setoid rewriting now rewrites under primitive projections.
  In rare cases (see for instance
  `#20575 <https://github.com/rocq-prover/rocq/issues/20575>`_),
  some rewrite that used to accidentally work will now correctly fail
  (`#19811 <https://github.com/rocq-prover/rocq/pull/19811>`_,
  by Josselin Poiret and Pierre-Marie Pédrot).
