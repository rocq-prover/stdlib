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

def component_requires(a, b):
    return is_component(a) and \
            (a == b or any(component_requires(m, b) for m in dependencies[a]))

component : dict[str, str] = {}
postorder : dict[str, int] = {}
def dfs(target, comp):
    if target in component.keys():
        assert component_requires(comp, component[target]),\
               f"{target} (from component {component[target]}) used in {comp}"+\
               f"but {comp} does not require {component[target]}"
        return
    component[target] = comp
    for dep in filter(is_component, dependencies[target]):
        dfs(dep, dep)
    for dep in dependencies[target]:
        dfs(dep, comp)
    postorder[target] = max(postorder.values(), default=0)+1
    if is_component(target):
        minimal = []
        for dep in sorted(filter(is_component, dependencies[target]), key=postorder.__getitem__, reverse=True):
            if not any(component_requires(e, dep) for e in minimal):
                minimal.append(dep)
        p = lambda s: s.split("/")[-1].removesuffix(".v")
        print ('\n'.join(f"{p(target)} -> {p(dep)}" for dep in minimal))
        print (f"({" ".join(sorted([p(k) for k,v in component.items() if v == target]))})")

top = 'subcomponents/all.v'
dfs(top, top)
for target in sorted(dependencies.keys()):
    if target == top or target == 'theories/All/All.v':
        assert component.get(target) == top
        continue
    assert component.get(target) not in [None, top],\
            f"{target} does not belong to any component"


# for target in dependencies.keys():
#     for dep in dependencies[target]:
#         if is_component(target) and not is_component(dep):
#             assert dep not in component.keys(), f"{dep} duplicated in components {target} and {component[dep]}"
#             component[dep] = target
# 
# def allowed(target, dep):
#     if is_component(target) or target in dependencies[component[target]]:
#         return True
#     subcomponents = filter(is_component, dependencies[component[target]])
#     return any(allowed(sub, dep) for sub in dependencies[component[target]])
# 
# for target in sorted(dependencies.keys()):
#     for dep in sorted(dependencies[target]):
#         assert allowed(target, dep), f"{dep} not allowed in {target} (component {component[target]})"
