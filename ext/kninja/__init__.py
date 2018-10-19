import kninja.ninja.ninja_syntax
import os
import sys

def basename_no_ext(path):
    return os.path.splitext(os.path.basename(path))[0]
def is_subpath(path, parent):
    return os.path.abspath(path).startswith(os.path.abspath(parent) + os.sep)

class Target():
    def __init__(self, proj, path):
        self.proj = proj
        self.path = path

    def __str__(self):
        return self.path

    def then(self, rule):
        target = rule.get_build_edge_target_path(self)
        return rule.build_edge(self.proj, self, target)

    def alias(self, alias):
        self.proj.build(alias, 'phony', self.path)
        return self

    def default(self):
        self.proj.default(self.path)
        return self

    @staticmethod
    def to_paths(value):
        if value is None:
            return None
        if isinstance(value, list):
            return list(map(Target.to_paths, value))
        if isinstance(value, str):
            return value
        if isinstance(value, Target):
            return value.path

class KDefinition(Target):
    def __init__(self, proj, kompiled_dirname, target):
        self._directory = os.path.dirname(kompiled_dirname)
        assert(self.directory(os.path.basename(kompiled_dirname), 'timestamp') == target)
        super().__init__(proj, target)

    def directory(self, *path):
        return os.path.join(self._directory, *path)

    def krun(self, krun_flags = None):
        return self.proj.rule( 'krun'
                             , description = 'Running $in ($directory)'
                             , command = '$k_bindir/krun $flags --debug --directory $directory $in > $out'
                             , ext = 'krun'
                             ) \
                             .variables(directory = self.directory()) \
                             .implicit(self.path)

    def kast(self):
        return self.proj.rule( 'kast'
                             , description = 'kast $in ($directory)'
                             , command     = '"$k_bindir/kast" $flags --debug --directory "$directory" "$in" > "$out"'
                             , ext = 'kast'
                             ) \
                             .variables(directory = self.directory()) \
                             .implicit(self.path)


class Rule():
    def __init__(self, name, description, command, ext = None):
        self.name = name
        self.description = description
        self.command = command
        self._ext = ext

        self._output           = None
        self._implicit         = None
        self._implicit_outputs = None
        self._pool             = None
        self._variables        = {}

    def ext(self, ext)                          : self._ext              = ext              ; return self
    def output(self, output)                    : self._output           = output           ; return self
    def implicit(self, implicit)                : self._implicit         = implicit         ; return self
    def implicit_outputs(self, implicit_outputs): self._implicit_outputs = implicit_outputs ; return self
    def pool(self, pool)                        : self._pool             = pool             ; return self
    def variables(self, **variables):
        # Merge the two dictionaries
        self._variables = { **self._variables, **variables }
        return self

    def get_build_edge_target_path(self, source):
        if self._output: return self._output
        if self._ext:
            path = source.path
            if not(is_subpath(path, source.proj.builddir(''))):
                # TODO: This is very simplistic, assumes that all paths are
                # relative to topdir, or are prefixed with builddir
                path = source.proj.builddir(path)
            return path + '.' + self._ext
        raise ValueError("Dont know how to generate target path for rule '%s'" % (self.name))

    def build_edge(self, proj, source, target):
        proj.build( rule = self.name
                  , inputs = source.path, outputs = target, implicit = Target.to_paths(self._implicit)
                  , implicit_outputs = self._implicit_outputs, pool = self._pool, variables = self._variables
                  )
        return Target(proj, target)

class KompileRule(Rule):
    def __init__(self):
        super().__init__('kompile', 'foo', 'bar')

    def output(self, output):
        raise ValueError("Cannot set ouput for Kompile -- use the directory variable instead")

    def kompiled_dirname(self, source):
        return self._variables.get('directory') + '/' + basename_no_ext(source.path) + '-kompiled'

    def get_build_edge_target_path(self, source):
        return  self.kompiled_dirname(source) + '/timestamp'

    def build_edge(self, proj, source, target):
        super().build_edge(proj, source, target)
        return KDefinition(proj, self.kompiled_dirname(source), target)

# KProject
# ========
#
# A KProject manages a single `ninja` build file.

class KProject(ninja.ninja_syntax.Writer):
    def __init__(self):
        if not os.path.exists(self.builddir()):
            os.mkdir(self.builddir())
        super().__init__(open(self.builddir('generated.ninja'), 'w'))
        self.generate_ninja()

        self.written_rules = {}

# Directory Layout
# ================
#
# Users may subclass KProjects, and override these methods for alternate project
# layouts.

# Dependency Paths
# ----------------

# Directory for storing submodules used by KNinja
    def extdir(self, *paths):
        return os.path.join('ext', *paths)

# Path to the K Framework
    def krepodir(self, *paths):
        return self.extdir('k', *paths)

# Directory where K binaries are stored
    def kbindir(self, *paths):
        return self.krepodir("k-distribution/target/release/k/bin/", *paths)

# Path to the KNinja project
    def kninjadir(self, *paths):
        return os.path.join(os.path.dirname(__file__), *paths)

# Build Paths
# -----------

# The project's main build directory
    def builddir(self, *paths):
        return os.path.join('.build', *paths)

# Directory to output tangled files in
    def tangleddir(self, *paths):
        return self.builddir('tangled', *paths)

# Directory to build OPAM in. We use this instead of `~/.opam` so that we don't
# intefere with system functionality.
    def opamroot(self, *paths):
        return self.builddir('opam', *paths)

# Generating the Ninja build script
# =================================

    def generate_ninja(self):
        self.comment('This is a generated file')
        self.include(self.kninjadir("prelude.ninja"))
        self.newline()
        self.variable('builddir', self.builddir())
        # TODO: Remove underscores for consistancy
        self.variable('opam_root', self.opamroot())
        self.variable('k_repository', self.krepodir())
        self.variable('k_bindir', self.kbindir())
        self.variable('tangle_repository', self.extdir('pandoc-tangle'))
        self.build_k()

    def build_k(self):
        self.build(self.krepodir(".git"), "git-submodule-init")
        self.build(self.kbindir("kompile"), "build-k", self.krepodir(".git"))
        self.build(self.extdir('pandoc-tangle', ".git"), "git-submodule-init")

    def build_ocaml(self):
        self.include(self.kninjadir('build-ocaml.ninja'))
        self.default('ocaml-deps')

    def rule(self, name, description, command, ext = None):
        rule = Rule(name, description, command, ext)
        if not(name in self.written_rules):
            super().rule(name, description = description, command = command)
            self.written_rules[name] = rule
        return rule

    def source(self, path):
        return Target(self, path)

    def tangle(self, tangle_selector = '.k'):
        return self.rule( 'tangle',
                          description = 'Tangling $in',
                          command     = 'LUA_PATH=$tangle_repository/?.lua '
                                      + 'pandoc $in -o $out --metadata=code:$tangle_selector --to "$tangle_repository/tangle.lua"'
                        ) \
                   .variables(tangle_selector = tangle_selector) \

    def kompile(self):
        self.rule( 'kompile'
                 , description = 'Kompiling $in ($backend)'
                 , command     = '$k_bindir/kompile --backend $backend --debug $flags '
                               + '--directory $$(dirname $$(dirname $out)) $in'
                 )
        return KompileRule().implicit(['ocaml-deps'])

    def kdefinition_no_build(self, name, kompiled_dirname, alias):
        return KDefinition(self, name, self.builddir(name), kompiled_dirname, alias)

    def check(self, expected):
        return self.rule( 'check-test-result'
                        , description = 'Checking $in'
                        , command = 'git diff --no-index $in $expected'
                        , ext = 'test') \
                   .variables(expected = expected) \
                   .implicit([expected])
