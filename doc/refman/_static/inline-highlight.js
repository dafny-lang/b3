document.addEventListener('DOMContentLoaded', function() {
  // Note, these reserved words are duplicated in doc/refman/b3_pygments.py
  const b3Keywords = [
    // top-level declarations
    'type',
    'tagger',
    'function',
    'axiom',
    'procedure',
    'domain',
    // statements
    'var',
    'val',
    'reinit',
    'exit',
    'return',
    'check',
    'assume',
    'reach',
    'assert',
    'probe',
    'forall',
    'choose', 'or',
    'if', 'else', 'case',
    'loop',
    // expressions
    'then',
    'exists',
    'false',
    'true',
    'old',
    'div',
    'mod',
    // types
    'bool',
    'int',
    // modifiers
    'for',
    'injective', 'tag', 'when',
    'explains',
    'inout', 'out', 'requires', 'ensures',
    'invariant',
    'pattern',
    'autoinv',
  ];

  document.querySelectorAll('code.docutils.literal.notranslate span.pre').forEach(function(span) {
      if (b3Keywords.includes(span.textContent.trim())) {
          span.classList.add('b3-keyword');
      }
  });
});
