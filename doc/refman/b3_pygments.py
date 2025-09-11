from pygments.lexer import RegexLexer, words
from pygments.token import *

b3_keywords = (
    # top-level declarations
    'type',
    'tagger',
    'function',
    'axiom',
    'procedure',
    # statements
    'var',
    'val',
    'exit',
    'return',
    'check',
    'assume',
    'assert',
    'probe',
    'forall',
    'choose', 'or',
    'if', 'else', 'case',
    'loop',
    # expressions
    'then',
    'exists',
    'false',
    'true',
)

b3_types = (
    'bool',
    'int',
)

b3_modifier = (
    'for',
    'injective', 'tag', 'when',
    'explains',
    'inout', 'out', 'requires', 'ensures',
    'invariant',
    'pattern',
)

class CustomLexer(RegexLexer):
    name = 'B3'
    aliases = ['b3']
    filenames = ['*.b3']
    tokens = {
        'root': [
            (r' ', Text),
            (r'\n', Text),
            (r'\r', Text),
            (r'//.*\n', Comment),
            (r'\([*]([^*]|[*]+[^)])*[*]+\)', Comment),
            (words(b3_keywords, suffix=r'\b'), Keyword),
            (words(b3_types, suffix=r'\b'), Keyword.Type),
            (words(b3_modifier, suffix=r'\b'), Keyword.Reserved),
            (r'[a-zA-Z][a-zA-Z_0-9$.]*', Name),
            (r'[0-9]+', Literal),
            (r'[a-zA-Z_0-9]+', Text),
            (r'.', Text),
        ]
    }
