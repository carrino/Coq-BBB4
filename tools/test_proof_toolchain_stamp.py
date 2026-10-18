#!/usr/bin/env python3
"""Toolchain identities and real Make cleanup operations with metadata stubs.

No Coq proof or OCaml compilation is performed.  The separate full-project
smoke uses the installed coq_makefile/coqtop metadata paths in a copied fixture.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

TOOLS = Path(__file__).resolve().parent
MAKEFILE = TOOLS.parent / "Makefile"
BRANCHES = ("_proof-all-run", "_proof-tr-all-run")


def preparation_makefile(text, branch):
    """Use the production cleanup and exact recipe prefix, stopping before work."""
    clean_start = text.index("clean:\n")
    clean_end = text.index("\n.PHONY: all clean", clean_start)
    start = text.index(branch + ":\n")
    stop = ("\t$(_state_time) state-build" if branch == "_proof-all-run"
            else "\t$(MAKE) Makefile.coq\n")
    end = text.index(stop, start)
    return (text[clean_start:clean_end] + "\n" + text[start:end]
            + "\t@touch continued\n.PHONY: " + branch + " clean\n")


COQC = '''#!/usr/bin/env python3
import json, os, pathlib, sys
if os.environ.get('FAIL_PROBE') == 'coqc': sys.exit(7)
c = json.loads(pathlib.Path(os.environ['FAKE_CONFIG']).read_text())
if sys.argv[1:] == ['--version']:
    print('The Coq Proof Assistant, version 8.18.0\\ncompiled with OCaml 4.14.2')
elif sys.argv[1:] == ['-config']:
    for k, v in c['coq'].items(): print(k + '=' + v)
else: sys.exit('unexpected Coq invocation: ' + repr(sys.argv))
'''
FINDLIB = '''#!/usr/bin/env python3
import json, os, pathlib, sys
if os.environ.get('FAIL_PROBE') == 'ocaml': sys.exit(8)
if sys.argv[1:] != ['opt', '-config']: sys.exit('unexpected findlib invocation')
c = json.loads(pathlib.Path(os.environ['FAKE_CONFIG']).read_text())
for k, v in c['ocaml'].items(): print(k + ': ' + v)
'''
GENERATOR = '''#!/usr/bin/env python3
import json, os, pathlib, shlex, sys
if sys.argv[1:] != ['-f', '_CoqProject', '-o', 'Makefile.coq']:
    sys.exit('unexpected coq_makefile invocation')
p = pathlib.Path('generate-count')
n = int(p.read_text()) + 1 if p.exists() else 1
p.write_text(str(n))
if os.environ.get('FAIL_GENERATE') in ('always', str(n)): sys.exit(9)
artifacts = json.loads(pathlib.Path('registered-artifacts.json').read_text())
body = 'cleanall:\\n\\t@echo clean >> cleanup-events\\n'
if os.environ.get('FAIL_CLEAN'): body += '\\t@false\\n'
body += '\\trm -f ' + ' '.join(shlex.quote(p) for p in artifacts) + '\\n'
pathlib.Path('Makefile.coq').write_text(body)
pathlib.Path('Makefile.coq.conf').write_text('# fixture\\n')
'''


class ToolchainStampTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.bin = self.root / "bin"
        self.lib = self.root / "lib"
        self.bin.mkdir()
        self.lib.mkdir()
        (self.root / "tools").mkdir()
        shutil.copy2(TOOLS / "proof_toolchain_stamp.py", self.root / "tools")
        for name, body in (("coqc", COQC), ("ocamlfind", FINDLIB),
                           ("coq_makefile", GENERATOR)):
            path = self.bin / name
            path.write_text(body)
            path.chmod(0o755)
        self.config = {
            "coq": {"COQLIB": str(self.lib / "coq"),
                    "COQCORELIB": str(self.lib / "coq-core"),
                    "DOCDIR": str(self.root / "doc"),
                    "OCAMLFIND": str(self.bin / "ocamlfind"),
                    "HASNATDYNLINK": "true", "COQ_NATIVE_COMPILER_DEFAULT": "yes"},
            "ocaml": {"version": "4.14.2", "flambda": "false",
                      "architecture": "amd64", "word_size": "64",
                      "standard_library": str(self.lib),
                      "standard_library_default": str(self.lib),
                      "cmx_magic_number": "Caml1999Y031",
                      "cmxa_magic_number": "Caml1999Z031",
                      "cmxs_magic_number": "Caml1999D031"},
        }
        self.env = dict(os.environ, PATH=str(self.bin) + os.pathsep + os.environ['PATH'],
                        FAKE_CONFIG=str(self.root / "config.json"))
        for key in ("OCAMLPARAM", "FAIL_PROBE", "FAIL_CLEAN", "FAIL_GENERATE",
                    "MAKEFLAGS", "MFLAGS", "MAKEOVERRIDES"):
            self.env.pop(key, None)
        self.save_config()
        self.artifacts = ["theories/A" + ext for ext in (".vo", ".vos", ".vok", ".glob")]
        self.artifacts += ["theories/.coq-native/NBBB4_A" + ext
                           for ext in (".cmi", ".cmx", ".cmxs")]
        self.extra_artifacts = [
            "theories/CensusTr/Compute/UnitTr_old.vo",
            "theories/CloseoutTr/CloseoutFinalTr.vo", "theories/CloseoutTr/BBBT4_Value.vo",
            "theories/Closeout/CloseoutFinal.vo", "theories/Closeout/CloseoutFinal.glob",
            "theories/Closeout/BBB4_Theorem.vo", "theories/Closeout/BBB4_Theorem.glob",
            "theories/Closeout/BBB4_Value.vo", "theories/Closeout/BBB4_Value.glob",
        ]
        self.keep = ["theories/A.v", "theories/UserScratch.v",
                     "theories/UserScratch.ml", "theories/UserScratch.vo",
                     "theories/.coq-native/user.native", "theories/.coq-native/user.ml"]
        for name in self.artifacts + self.extra_artifacts + self.keep:
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("fixture " + name + "\n")
        (self.root / "_CoqProject").write_text("-Q theories BBB4\ntheories/A.v\n")
        (self.root / "registered-artifacts.json").write_text(json.dumps(self.artifacts))

    def tearDown(self):
        self.tmp.cleanup()

    def save_config(self):
        (self.root / "config.json").write_text(json.dumps(self.config))

    def run_command(self, argv):
        return subprocess.run(argv, cwd=self.root, env=self.env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20)

    def identity(self):
        result = self.run_command([sys.executable, "tools/proof_toolchain_stamp.py"])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout.rstrip("\n")

    def prepare(self, branch):
        (self.root / "Makefile").write_text(preparation_makefile(MAKEFILE.read_text(), branch))
        return self.run_command(["make", "--no-print-directory", branch])

    def assert_sources_preserved(self):
        for name in self.keep:
            self.assertEqual((self.root / name).read_text(), "fixture " + name + "\n")

    def assert_cleaned(self):
        for name in self.artifacts + self.extra_artifacts:
            self.assertFalse((self.root / name).exists(), name)
        self.assert_sources_preserved()
        self.assertTrue((self.root / "Makefile.coq").is_file())
        self.assertTrue((self.root / "continued").is_file())

    def test_same_versions_variant_and_native_magic_change_stamp(self):
        old = self.identity()
        self.config["ocaml"].update(flambda="true", cmx_magic_number="Caml1999y031",
                                     cmxa_magic_number="Caml1999z031")
        self.save_config()
        new = self.identity()
        self.assertNotEqual(old, new)
        self.assertEqual(json.loads(old)["coq"], json.loads(new)["coq"])

    def test_same_variant_magic_change_is_not_ignored(self):
        old = self.identity()
        self.config["ocaml"]["cmxs_magic_number"] = "different"
        self.save_config()
        self.assertNotEqual(old, self.identity())

    def test_native_default_and_coq_executable_contents_are_identity(self):
        old = self.identity()
        self.config["coq"]["COQ_NATIVE_COMPILER_DEFAULT"] = "ondemand"
        self.save_config()
        changed_default = self.identity()
        self.assertNotEqual(old, changed_default)
        with (self.bin / "coqc").open("a") as stream:
            stream.write("\n# changed executable with the same version\n")
        self.assertNotEqual(changed_default, self.identity())

    def test_actual_configured_findlib_not_path_ocamlopt(self):
        (self.bin / "ocamlopt").write_text("#!/bin/sh\nexit 99\n")
        (self.bin / "ocamlopt").chmod(0o755)
        self.identity()

    def test_prefix_only_move_of_identical_inputs_does_not_invalidate(self):
        old = self.identity()
        other = self.root / "relocated"
        other.mkdir()
        for name in ("coqc", "ocamlfind"):
            shutil.copy2(self.bin / name, other / name)
        self.env["PATH"] = str(other) + os.pathsep + self.env["PATH"]
        self.config["coq"].update(COQLIB=str(other), COQCORELIB=str(other),
                                    DOCDIR=str(other), OCAMLFIND=str(other / "ocamlfind"))
        self.config["ocaml"].update(standard_library=str(other),
                                      standard_library_default=str(other))
        self.save_config()
        self.assertEqual(old, self.identity())

    def test_optimizer_environment_is_data_never_evaluated(self):
        old = self.identity()
        self.env["OCAMLPARAM"] = ""
        empty = self.identity()
        self.assertNotEqual(old, empty)
        self.env["OCAMLPARAM"] = "_,Oclassic=0,O3=1;$(touch forbidden)"
        self.assertNotEqual(empty, self.identity())
        self.assertFalse((self.root / "forbidden").exists())

    def test_internal_compiler_parameter_file_is_content_sensitive(self):
        old = self.identity()
        path = self.lib / "ocaml_compiler_internal_params"
        path.write_text("* : Oclassic = 1\n")
        first = self.identity()
        path.write_text("* : Oclassic = 0\n")
        self.assertNotEqual(old, first)
        self.assertNotEqual(first, self.identity())

    def test_probe_and_missing_required_field_fail_without_stamp(self):
        for fail in ("coqc", "ocaml"):
            with self.subTest(fail=fail):
                self.env["FAIL_PROBE"] = fail
                result = self.run_command([sys.executable, "tools/proof_toolchain_stamp.py"])
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
        self.env.pop("FAIL_PROBE")
        del self.config["ocaml"]["flambda"]
        self.save_config()
        result = self.run_command([sys.executable, "tools/proof_toolchain_stamp.py"])
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")

    def test_both_branches_migrate_legacy_stamp_and_missing_makefile(self):
        for branch in BRANCHES:
            with self.subTest(branch=branch):
                for name in self.artifacts + self.extra_artifacts:
                    path = self.root / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text("old object\n")
                (self.root / "Makefile.coq").unlink(missing_ok=True)
                (self.root / ".toolchain-stamp").write_text("Coq 8.18 OCaml 4.14.2|yes\n")
                result = self.prepare(branch)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assert_cleaned()
                self.assertEqual((self.root / ".toolchain-stamp").read_text(), self.identity() + "\n")

    def test_missing_stamp_cleans_existing_artifacts(self):
        result = self.prepare(BRANCHES[0])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assert_cleaned()

    def test_matching_stamp_preserves_artifacts_but_regenerates_makefile(self):
        (self.root / ".toolchain-stamp").write_text(self.identity() + "\n")
        (self.root / "Makefile.coq").write_text("stale contents\n")
        result = self.prepare(BRANCHES[0])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        for name in self.artifacts:
            self.assertTrue((self.root / name).exists(), name)
        self.assertFalse((self.root / "cleanup-events").exists())
        self.assertEqual((self.root / "generate-count").read_text(), "1")
        self.assertIn("cleanall:", (self.root / "Makefile.coq").read_text())

    def test_mismatch_uses_current_project_not_stale_makefile(self):
        (self.root / ".toolchain-stamp").write_text("old\n")
        (self.root / "Makefile.coq").write_text("cleanall:\n\t@false\n")
        result = self.prepare(BRANCHES[0])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assert_cleaned()
        self.assertEqual((self.root / "generate-count").read_text(), "2")

    def test_actual_same_version_variant_mismatch_cleans(self):
        (self.root / ".toolchain-stamp").write_text(self.identity() + "\n")
        self.config["ocaml"]["flambda"] = "true"
        self.save_config()
        result = self.prepare(BRANCHES[1])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assert_cleaned()

    def test_state_first_migration_also_invalidates_direct_tr_objects(self):
        (self.root / ".toolchain-stamp").write_text("old shared toolchain\n")
        state = self.prepare(BRANCHES[0])
        self.assertEqual(state.returncode, 0, state.stdout + state.stderr)
        self.assert_cleaned()
        stamp = (self.root / ".toolchain-stamp").read_text()
        events = (self.root / "cleanup-events").read_text()
        tr = self.prepare(BRANCHES[1])
        self.assertEqual(tr.returncode, 0, tr.stdout + tr.stderr)
        self.assertEqual((self.root / ".toolchain-stamp").read_text(), stamp)
        self.assertEqual((self.root / "cleanup-events").read_text(), events)
        self.assert_cleaned()

    def test_unreadable_vo_and_orphan_native_outputs_are_removed(self):
        # Model cleanall's failed native-name discovery: it removes the .vo,
        # but has no native filenames.  The explicit cache pass must finish.
        names = [p for p in self.artifacts if ".coq-native" not in p]
        (self.root / "registered-artifacts.json").write_text(json.dumps(names))
        orphan = self.root / "theories/.coq-native/NObsolete_Module.o"
        orphan.write_text("old native object")
        (self.root / "theories/A.vo").write_bytes(b"unreadable old ABI header")
        (self.root / ".toolchain-stamp").write_text("old ABI\n")
        result = self.prepare(BRANCHES[0])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assert_cleaned()
        self.assertFalse(orphan.exists())

    def test_compiled_cache_symlink_is_unlinked_without_touching_target(self):
        target = self.root / "user-object.o"
        target.write_text("external object to preserve")
        link = self.root / "theories/.coq-native/NObsolete.o"
        link.symlink_to(target)
        result = self.prepare(BRANCHES[0])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertFalse(link.is_symlink())
        self.assertEqual(target.read_text(), "external object to preserve")

    def test_directory_symlinks_are_not_followed(self):
        with tempfile.TemporaryDirectory() as outside:
            external = Path(outside) / ".coq-native"
            external.mkdir()
            artifact = external / "NExternal.cmxs"
            artifact.write_text("preserve outside project")
            (self.root / "linked-directory").symlink_to(outside, target_is_directory=True)
            result = self.prepare(BRANCHES[0])
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(artifact.read_text(), "preserve outside project")

    def test_unsafe_cache_directory_symlink_blocks_new_stamp(self):
        with tempfile.TemporaryDirectory() as outside:
            (self.root / "unsafe").mkdir()
            (self.root / "unsafe/.coq-native").symlink_to(outside, target_is_directory=True)
            (self.root / ".toolchain-stamp").write_text("old\n")
            result = self.prepare(BRANCHES[1])
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual((self.root / ".toolchain-stamp").read_text(), "old\n")
            self.assertFalse((self.root / "continued").exists())
            self.assert_sources_preserved()

    def test_unsafe_cache_is_rejected_before_generated_clean_runs(self):
        with tempfile.TemporaryDirectory() as outside:
            target = Path(outside) / "NOutside.cmxs"
            target.write_text("must survive ordinary clean preflight")
            (self.root / "unsafe").mkdir()
            cache = self.root / "unsafe/.coq-native"
            cache.symlink_to(outside, target_is_directory=True)
            # An ordinary generated rm would traverse this cache symlink.
            names = self.artifacts + ["unsafe/.coq-native/NOutside.cmxs"]
            (self.root / "registered-artifacts.json").write_text(json.dumps(names))
            (self.root / ".toolchain-stamp").write_text("old\n")
            result = self.prepare(BRANCHES[0])
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse((self.root / "cleanup-events").exists())
            self.assertEqual(target.read_text(), "must survive ordinary clean preflight")
            self.assertEqual((self.root / ".toolchain-stamp").read_text(), "old\n")

    def test_unhandled_cache_entry_blocks_new_stamp(self):
        nested = self.root / "theories/.coq-native/user-directory"
        nested.mkdir()
        (nested / "user.v").write_text("preserve nested source")
        (self.root / ".toolchain-stamp").write_text("old\n")
        result = self.prepare(BRANCHES[0])
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual((self.root / ".toolchain-stamp").read_text(), "old\n")
        self.assertEqual((nested / "user.v").read_text(), "preserve nested source")
        self.assertFalse((self.root / "continued").exists())
        self.assert_sources_preserved()


    def test_probe_generate_clean_failures_never_approve_or_continue(self):
        for branch in BRANCHES:
            for key, value in (("FAIL_PROBE", "ocaml"), ("FAIL_GENERATE", "always"),
                               ("FAIL_CLEAN", "1")):
                with self.subTest(branch=branch, failure=key):
                    (self.root / ".toolchain-stamp").write_text("old\n")
                    (self.root / "continued").unlink(missing_ok=True)
                    self.env[key] = value
                    result = self.prepare(branch)
                    self.env.pop(key)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual((self.root / ".toolchain-stamp").read_text(), "old\n")
                    self.assertFalse((self.root / "continued").exists())
                    self.assert_sources_preserved()

    def test_failure_after_cleanup_keeps_old_stamp(self):
        (self.root / ".toolchain-stamp").write_text("old\n")
        self.env["FAIL_GENERATE"] = "2"
        result = self.prepare(BRANCHES[1])
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual((self.root / ".toolchain-stamp").read_text(), "old\n")
        self.assertFalse((self.root / "continued").exists())
        self.assert_sources_preserved()


if __name__ == "__main__":
    unittest.main()
