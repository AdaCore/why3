import re
from docutils import nodes
from sphinx import addnodes
from sphinx.roles import XRefRole
from sphinx.util.docutils import SphinxDirective

ws_re = re.compile(r'\s+')

class Why3ToolRole(XRefRole):
    def process_link(self, env, refnode, has_explicit_title, title, target):
        target = ws_re.sub(' ', target)
        if target.startswith('why3 '):
            target = target[5:]
        return title, target

def setup(app):
    app.add_object_type('why3-transform', 'why3-transform', 'pair: %s; transformation')
    app.add_crossref_type('why3-tool', 'why3-tool', 'pair: %s; tool')
    app.add_role_to_domain('std', 'why3-tool', Why3ToolRole(), override = True)

    return {
        'version': '0.1',
        'parallel_read_safe': True,
        'parallel_write_safe': True,
    }
