import re
from docutils import nodes
from sphinx import addnodes
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

class Why3Domain(Domain):
    name = 'why3'
    label = 'Why3'
    roles = {
        'tool': Why3ToolRole(),
    }
    directives = {
        'tool': Why3ToolDirective,
    }
    indices = {
    }
    initial_data = {}
    initial_data['objects'] = {
        'tool': {},
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
    app.add_object_type('why3-transform', 'why3-transform', 'pair: %s; transformation')
    app.add_domain(Why3Domain)

    return {
        'version': '0.1',
        'parallel_read_safe': True,
        'parallel_write_safe': True,
    }
