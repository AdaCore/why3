from pygments.lexer import RegexLexer, words
from pygments.token import Text, Comment, Operator, Keyword, Name, String, Number, Punctuation, Error

class WhyMLLexer(RegexLexer):
    name = 'WhyML'
    aliases = 'whyml'

    keywords = (
        'abstract', 'absurd', 'alias', 'any', 'as', 'assert', 'assume', 'at', 'axiom',
        'begin', 'break', 'by', 'check', 'clone', 'coinductive', 'constant', 'continue',
        'diverges', 'do', 'done', 'downto',
        'else', 'end', 'ensures', 'epsilon', 'exception', 'exists', 'export',
        'false', 'float', 'for', 'forall', 'fun', 'function', 'ghost', 'goal',
        'if', 'import', 'in', 'inductive', 'invariant', 'label', 'lemma', 'let',
        'match', 'meta', 'module', 'mutable', 'not', 'old',
        'partial', 'predicate', 'private', 'pure',
        'raise', 'raises', 'range', 'reads', 'rec', 'ref', 'requires', 'return', 'returns',
        'scope', 'so', 'then', 'theory', 'to', 'true', 'try', 'type', 'use', 'val', 'variant',
        'while', 'with', 'writes',
    )

    tokens = {
        'root': [
            (r'\s+', Text),
            (r'\(\*\)', Operator),
            (r'\(\*', Comment, 'comment'),
            (r'\[@[^]]*\]', Comment),
            (words(keywords, suffix=r'\b'), Keyword),
            (r'[-~!%^&*+=|?<>/\\]', Operator),
            (r'[][{};:.,()]', Punctuation),
            (r"[^\W\d][\w']*", Name),
            (r'\bresult\b', Name.Builtin.Pseudo),

            (r'-?\d\d*([.]\d*)?([eE][+-]?\d\d*)', Number.Float),
            (r'-?0[xX][\da-fA-F][\da-fA-F]*([.][\da-fA-F]*)?([pP][+-]?\d\d*)', Number.Float),
            (r'0[xX][\da-fA-F][\da-fA-F_]*', Number.Hex),
            (r'0[oO][0-7][0-7_]*', Number.Oct),
            (r'0[bB][01][01_]*', Number.Bin),
            (r'\d[\d_]*', Number.Integer),

            (r"'", Keyword),
            (r'"', String.Double, 'string'),
        ],
        'comment': [
            (r'[^(*)]+', Comment),
            (r'\(\*', Comment, '#push'),
            (r'\*\)', Comment, '#pop'),
            (r'[(*)]', Comment),
        ],
        'string': [
            (r'[^\\"]+', String.Double),
            (r'\\[\\"\'ntbr]', String.Escape),
            (r'\\[0-9]{3}', String.Escape),
            (r'\\x[0-9a-fA-F]{2}', String.Escape),
            (r'\\\n', String.Double),
            (r'"', String.Double, '#pop'),
        ],
    }

from sphinx.highlighting import lexers

lexers['whyml'] = WhyMLLexer(startinline=True)

import re
from docutils import nodes
from sphinx import addnodes
from sphinx.directives import ObjectDescription
from sphinx.domains import Domain
from sphinx.roles import XRefRole
from sphinx.util.docutils import SphinxDirective
from sphinx.util.nodes import make_refnode

ws_re = re.compile(r'\s+')

class Why3ToolRole(XRefRole):
    def process_link(self, env, refnode, has_explicit_title, title, target):
        target = ws_re.sub(' ', target)
        if target.startswith('why3 '):
            target = target[5:]
        return title, target

attr_re = re.compile(r'\[@(.*)\]')

class Why3AttributeRole(XRefRole):
    def process_link(self, env, refnode, has_explicit_title, title, target):
        target = ws_re.sub(' ', target)
        m = attr_re.match(target)
        if m:
            target = m.group(1)
        return title, target

class Why3ToolDirective(SphinxDirective):
    has_content = False
    required_arguments = 1
    optional_arguments = 0
    final_argument_whitespace = True
    option_spec = {}

    def run(self):
        fullname = ws_re.sub(' ', self.arguments[0].strip())
        targetname = '%s-%s' % (self.name, fullname)
        node = nodes.target('', '', ids = [targetname])
        self.state.document.note_explicit_target(node)
        indexentry = '%s; command' % (fullname,)
        inode = addnodes.index(entries = [('pair', indexentry, targetname, '', None)])
        domain = self.env.get_domain('why3')
        domain.add_object('tool', fullname, targetname)
        return [inode, node]

class Why3Thing(ObjectDescription):
    has_content = True
    required_arguments = 1
    optional_arguments = 0
    final_argument_whitespace = True
    option_spec = {}
    thing_index = ''
    thing_kind = ''

    def handle_signature(self, sig, signode):
        signode += addnodes.desc_name(text = sig)
        return sig

    def add_target_and_index(self, name, sig, signode):
        targetname = '%s-%s' % (self.name, name)
        signode['ids'].append(targetname)
        indexentry = '%s; %s' % (name, self.thing_index)
        self.indexnode['entries'].append(('pair', indexentry, targetname, '', None))
        domain = self.env.get_domain('why3')
        domain.add_object(self.thing_kind, name, targetname)

class Why3Attribute(Why3Thing):
    thing_index = 'attribute'
    thing_kind = 'attribute'

class Why3Debug(Why3Thing):
    thing_index = 'debug flag'
    thing_kind = 'debug'

class Why3Meta(Why3Thing):
    thing_index = 'meta'
    thing_kind = 'meta'

class Why3Transform(Why3Thing):
    thing_index = 'transformation'
    thing_kind = 'transform'

class Why3Domain(Domain):
    name = 'why3'
    label = 'Why3'
    roles = {
        'attribute': Why3AttributeRole(),
        'debug': XRefRole(),
        'meta': XRefRole(),
        'tool': Why3ToolRole(),
        'transform': XRefRole(),
    }
    directives = {
        'attribute': Why3Attribute,
        'debug': Why3Debug,
        'meta': Why3Meta,
        'tool': Why3ToolDirective,
        'transform': Why3Transform,
    }
    indices = {
    }
    initial_data = {}
    initial_data['objects'] = {
        'attribute': {},
        'debug': {},
        'meta': {},
        'tool': {},
        'transform': {},
    }

    def get_objects(self):
        for role, objects in self.data['objects'].items():
            prio = 0 # self.object_types[role].attrs['searchprio']
            for name, (docname, targetname) in objects.items():
                yield (name, name, role, docname, targetname, prio)

    def resolve_xref(self, env, fromdocname, builder, role, targetname, node, contnode):
        resolved = self.data['objects'][role].get(targetname)
        if resolved:
            (todocname, targetname) = resolved
            return make_refnode(builder, fromdocname, todocname, targetname, contnode, targetname)
        return None

    def add_object(self, role, name, targetname):
        self.data['objects'][role][name] = (self.env.docname, targetname)


def setup(app):
    app.add_domain(Why3Domain)

    return {
        'version': '0.1',
        'parallel_read_safe': True,
        'parallel_write_safe': True,
    }
