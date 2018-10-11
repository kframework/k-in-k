import kninja.ninja.ninja_syntax
import os

def basename_no_ext(path):
    return os.path.splitext(os.path.basename(path))[0]

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

    def tangle(self, input, output):
        self.build(output, 'tangle', input, implicit = [ '$tangle_repository/.git' ])
        return output

    def kdefinition(self, name, main, backend, alias, kompile_flags = None):
        kdef = self.kdefinition_no_build( name
                                        , kompiled_dirname = basename_no_ext(main) + '-kompiled'
                                        , alias = alias
                                        )
        kdef.kompile(main, backend = backend, kompile_flags = kompile_flags)
        kdef.write_alias(alias)
        return kdef

    def kdefinition_no_build(self, name, kompiled_dirname, alias):
        return KDefinition(self, name, self.builddir(name), kompiled_dirname, alias)

class KDefinition:
    def __init__(self, writer, name, directory, kompiled_dirname, alias):
        self.writer           = writer
        self.name             = name
        self.directory        = directory
        self.kompiled_dirname = kompiled_dirname
        self.alias            = alias

    def get_timestamp_file(self):
        return self.kompileddir('timestamp')
    def kompileddir(self, *path):
        return os.path.join(self.directory, self.kompiled_dirname, *path)

    def write_alias(self, alias):
        # TODO: This assumes that the timestamp file exists. This is not the case
        # in when using the OCaml interpreter.
        self.writer.build(alias, 'phony', self.get_timestamp_file())

    def kompile(self, main, backend = 'java', kompile_flags = None):
        self.writer.build( self.get_timestamp_file()
                         , 'kompile'
                         , main
                         , variables = { 'backend' : backend
                                       , 'flags' : kompile_flags
                                       }
                         )

    def kast(self, output, input, kast_flags = None):
        return self.writer.build( outputs  = output
                                , rule     = 'kast'
                                , inputs   = input
                                , implicit = [self.alias]
                                , variables = { 'directory' : self.directory
                                              , 'flags'     : kast_flags
                                              }
                                )

    def krun(self, output, input, krun_flags = None):
        self.writer.build( outputs  = [output]
                         , rule     = 'krun'
                         , inputs   = [input]
                         , implicit = [self.alias]
                         , variables = { 'directory' : self.directory
                                       , 'flags'     : krun_flags
                                       }
                         )
        return output

    def check_actual_expected(self, name, actual, expected):
        return self.writer.build( outputs   = name
                                , rule      = 'check-test-result'
                                , inputs    = actual
                                , implicit  = expected
                                , variables = { 'expected' : expected }
                                )

    def krun_and_check(self, output_dir, input, expected, krun_flags = None):
        basename  = os.path.basename(input)
        actual    = os.path.join(output_dir, basename + '.' + self.name + '.actual')
        test_name = input + '.' + self.name + '.krun'
        self.writer.comment(input + ' (' + self.name + ')')
        self.krun( output = actual
                 , input  = input
                 , krun_flags = krun_flags
                 )

        self.check_actual_expected( name     = test_name
                                  , actual   = actual
                                  , expected = expected
                                  )
        self.writer.default(test_name)
        self.writer.newline()

