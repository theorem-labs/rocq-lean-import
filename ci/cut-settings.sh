# shellcheck shell=bash disable=SC2034
# (ci/build-9.2-cut.sh, which sources this file, reads every variable below.)
# ci/cut-settings.sh: what build_switch in ci/build-9.2-cut.sh builds the opam root from: the pins and settings of
# the switch "cut". The workflow .github/workflows/build-9.2-cut.yml keys its cache of that root on this file alone,
# so a change here, a comment included, builds the root again, and a change elsewhere does not. A change to
# build_switch itself that changes what it builds must therefore come with a change here.

# The Rocq commit the plugin is built and tested against (branch release/9.2/2026-11-15-speed-8.0.9).
CUT_ROCQ_REPO=https://github.com/theorem-labs/rocq.git
CUT_ROCQ_COMMIT=07e45e36f6e9966faa88bcc16fa5a1bd7bc34b72
ROCQ_VERSION=9.2.0 # the version the five Rocq packages are pinned at
ROCQ_STDLIB_VERSION=9.1.0
DUNE_VERSION=3.23.1
# The value of OCAML_SWITCH_PACKAGES in theorem-labs/grading-tools main docker/integration-test.Dockerfile,
# read 2026-11-24.
OCAML_SWITCH_PACKAGES=ocaml-variants.4.14.2+options,ocaml-option-flambda,ocaml-option-nnp
OPAM_REPOSITORY_URL=https://github.com/ocaml/opam-repository.git
OPAM_REPOSITORY_COMMIT=92ad3ffdce82239c0acb2f053fc49c02fc3b85c1
ROCQ_OPAM_URL=https://github.com/rocq-prover/opam.git # its released/ directory holds coq-stdlib
ROCQ_OPAM_COMMIT=4e872c3595f941e61beb2396064ef3d57dcc093d
# opam 2.3.0, downloaded to $CUT_ROOT/bin/opam only when no opam is on PATH.
OPAM_URL_X86_64=https://github.com/ocaml/opam/releases/download/2.3.0/opam-2.3.0-x86_64-linux
OPAM_SHA256_X86_64=324e78e3f33efeba279aacf9f9610cfec7b2df7d7e0e1640f75f09de85f96cc9
