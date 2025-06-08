import sys, os, functools
from glob import glob
from subprocess import Popen, PIPE, STDOUT

vs = glob('theories/**/*.v', recursive=True) + glob('subcomponents/*.v')
cmd = 'rocq dep -w +default -Q theories/ Stdlib -Q subcomponents subcomponents'
dependencies : dict[str, list[str]] = {}
with Popen(cmd.split() + vs, stdout=PIPE, text=True) as proc:
    for line in proc.stdout:
        is_vo = lambda s: s.endswith('.vo')
        (target,), deps = [filter(is_vo, s.split()) for s in line.split(":")]
        dependencies[target[:-1]] = sorted(d[:-1] for d in deps)
assert proc.returncode == 0

def is_component(target):
  return target.startswith('subcomponents/')

@functools.cache
def comp_requires(a, b):
    return a == b or any(comp_requires(m, b) for m in compdeps[a])

compdeps = {k : list(filter(is_component, vs)) for k, vs in dependencies.items()}
component : dict[str, str] = {}
postorder : dict[str, int] = {}
def dfs(target, comp, html, dot):
    if target in component.keys():
        assert comp_requires(comp, component[target]),\
               f"{target} (from component {component[target]}) used in {comp}"+\
               f"but {comp} does not require {component[target]}"
        return
    component[target] = comp
    for dep in compdeps[target]:
        dfs(dep, dep, html, dot)
    for dep in dependencies[target]:
        dfs(dep, comp, html, dot)
    if html.name == os.devnull and dot.name == os.devnull:
        return # not printing anything anyway
    postorder[target] = max(postorder.values(), default=0)+1
    if is_component(target):
        minimal = []
        for dep in sorted(compdeps[target], key=postorder.__getitem__, reverse=True):
            if not any(comp_requires(e, dep) for e in minimal):
                minimal.append(dep)
        p = lambda s: s.split("/")[-1].removesuffix(".v")
        print ('\n'.join(f"{p(target)} -> {p(dep)};" for dep in minimal), file=dot)
        name = p(target)
        print(f'<div class="subcomponent"><dt id="{name}">Subcomponent <a href="#{name}">{name}</a></dt><dd>', file=html)
        if minimal:
            deps = [f'<li><a href="#{m}">{m}</a></li>' for m in map(p, minimal)]
            print(f'depends on <ul class="component-dependencies">{" ".join(deps)}</ul> and ', file=html)
        print(f'contains <ul class="component-contents">', file=html)
        compfiles = [k for k,v in component.items() if v == target and k != target]
        for vfile in sorted(compfiles, key=postorder.__getitem__):
            m = vfile.removeprefix("theories/").replace("/", ".").removesuffix(".v")
            print(f'  <li><a href="Stdlib.{m}.html">{m}</a></li>', file=html)
        print(f'</ul></dd></div>\n', file=html)

html_header = r"""
<style>
div.subcomponent {
  padding-left: 2em;
  text-indent:-2em;
  dt {
    display : inline;
    margin-right: 0;
    a { text-decoration: inherit; }
  }
  dd {
    display: inline;
    margin-left: 0;
    margin-right: 0;
    ul {
      display: inline;
      padding-left: 0;
      li {
        display: inline;
      }
    }
  }
}
</style>
<dl>
"""


dot_header = r"""
digraph stdlib_deps {
	rankdir="BT";
	bgcolor="transparent";
	node [color="#ff540a",
		shape=rectangle,
		style=filled
		URL="#\N"
	];
	edge [color="#260085"];
"""

assert len(sys.argv) in [1,2,3]
with open(sys.argv[1] if 1 < len(sys.argv) else os.devnull, 'w') as html,\
     open(sys.argv[2] if 2 < len(sys.argv) else os.devnull, 'w') as dot:
  print(html_header, file=html)
  print(dot_header, file=dot)
  top = 'subcomponents/all.v'
  dfs(top, top, html, dot)
  for target in sorted(dependencies.keys()):
      if target == top or target == 'theories/All/All.v':
          assert component.get(target) == top
          continue
      assert component.get(target) not in [None, top],\
              f"{target} does not belong to any component"
  print("</dl>", file=html)
  print("}", file=dot)
