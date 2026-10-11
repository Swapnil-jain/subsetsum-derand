PYTHON ?= python3
.PHONY: check certs logic explicit stage3 stage4 stage5 stage5b tests lean lean-123 lean-stage4 lean-stage5 \
	lean-stage5b lean-sync all

# One command: every certificate against its committed transcript, every brute-force logic check, and the tests
# (one core, under 1 GB; about 20 minutes). Each script exits 0 only on PASS. Standard-library Python, except
# check_stage4.py and check_stage5.py, which need numpy (requirements.txt).
check: certs logic explicit stage3 stage4 stage5 stage5b tests

# Transcripts of the Stage 4 to 5b scripts are compared with their elapsed-time stamps " [123s]" removed.
NOTIME := sed -E 's/ \[[0-9]+s\]$$//'

certs:
	cd certificates && $(PYTHON) cert_gamma.py | cmp - cert_gamma.out && $(PYTHON) cert_eps.py | cmp - cert_eps.out
	@echo "certificates: PASS"

logic:
	cd certificates && $(PYTHON) check_stage1.py > /dev/null && $(PYTHON) check_stage2.py > /dev/null
	cd proofs/ye-li-audit && for f in yl_*.py; do $(PYTHON) $$f > /dev/null || exit 1; done
	@echo "logic checks: PASS"

# Stage 2b (explicit): the certificates against their transcripts (Theorem E; Secs. 12 and 13, smaller n0), and
# the gate-level toy test of Lemmas E1 to E4 at N = 8 (about 45 s, about 200 MB).
explicit:
	cd certificates && $(PYTHON) cert_explicit.py | cmp - cert_explicit.out && $(PYTHON) toy_explicit.py > /dev/null \
		&& $(PYTHON) cert_explicit_b16.py | cmp - cert_explicit_b16.out \
		&& $(PYTHON) cert_explicit_b17.py | cmp - cert_explicit_b17.out
	@echo "explicit (Stage 2b) certificates and toy test: PASS"

# Stage 3: the certificate against its transcript, the brute-force logic check and the gate-level test of the
# re-tuned Ye-Li circuit (about 3 min, < 200 MB).
stage3:
	cd certificates && $(PYTHON) cert_stage3.py | cmp - cert_stage3.out && $(PYTHON) check_stage3.py > /dev/null \
		&& $(PYTHON) check_circuit.py > /dev/null
	@echo "Stage 3 certificate, logic check and circuit test: PASS"

# Stage 4 (certificates/stage4): the certificate, the Stage 4+ family certificate and the brute force (about 7 min).
stage4:
	cd certificates/stage4 && $(PYTHON) -B cert_stage4.py | cmp - cert_stage4.out \
		&& $(PYTHON) -B cert_stage4plus.py | cmp - cert_stage4plus.out && $(PYTHON) -B check_stage4.py | cmp - check_stage4.out
	@echo "Stage 4 certificates and brute force: PASS"

# Stage 5 (certificates/stage5): the certificate and the brute force (about 3 min).
stage5:
	cd certificates/stage5 && $(PYTHON) -B cert_stage5.py | cmp - cert_stage5.out \
		&& $(PYTHON) -B check_stage5.py | cmp - check_stage5.out
	@echo "Stage 5 certificate and brute force: PASS"

# Stage 5b (certificates/stage5b): the certificate (about 4 min).
stage5b:
	cd certificates/stage5b && $(PYTHON) -B cert_stage5b.py | $(NOTIME) | cmp - cert_stage5b.out
	@echo "Stage 5b certificate: PASS"

# The README's headline numbers against the transcripts.
tests:
	$(PYTHON) -B -m unittest discover -s tests

# The generated Lean point files must be exactly what the generators produce from certificates/.
lean-sync:
	cd lean && $(PYTHON) gen_stage1.py > /dev/null && $(PYTHON) gen_stage2.py > /dev/null \
		&& $(PYTHON) gen_explicit.py > /dev/null && $(PYTHON) gen_stage3.py > /dev/null && $(PYTHON) gen_explicit_n0.py > /dev/null
	git diff --exit-code -- lean/SubsetsumLean && echo "lean sources in sync with certificates/: PASS"

# Lean 4 kernel check (lean/LEAN_SCOPE.md). Needs elan with Lean v4.34.1; fetches prebuilt Mathlib oleans
# (about 7 GB on disk), never compiles Mathlib. Every module is built one at a time under build_watch.sh (nice -n 19,
# one Lean thread, optional RSS abort (set LIMIT_MB=3072 on an 8 GB machine)). Every printed theorem must depend only on propext, Classical.choice and
# Quot.sound (or a subset of them): axioms_ok.sh checks that no #print axioms line is missing or non-standard.
# LONG: Stages 1-3 take about 4 minutes, Stage 4 about 30, Stage 5 about 70 and Stage 5b about 60 more on an
# 8 GB laptop.
lean: lean-123 lean-stage4 lean-stage5 lean-stage5b

# Stages 1 to 3: the Stage 2b theorems (Explicit.lean), the 42 smaller-n0 theorems of Secs. 12-13 (namespace SS.N0)
# and the Stage 3 theorems must be among the printed ones.
lean-123:
	cd lean && lake exe cache get && ./build_watch.sh build \
		&& ./build_watch.sh env lean SubsetsumLean/Axioms.lean > axioms.check \
		&& ./axioms_ok.sh axioms.check SubsetsumLean/Axioms.lean \
		&& grep -q "'SS.explicit_A' depends on axioms" axioms.check \
		&& test $$(grep -c "'SS.explicit_" axioms.check) -eq 13 \
		&& test $$(grep -c "'SS.s3_" axioms.check) -eq 34 && grep -q "'SS.s3_E3' depends" axioms.check \
		&& test $$(grep -c "'SS.N0\." axioms.check) -eq 42 \
		&& echo "lean (Stages 1-3): PASS (standard axioms only; Stage 2b certificates, Secs. 12-13 and Stage 3 included)"

lean-stage4:
	cd lean && lake exe cache get && ./check_stage4.sh

lean-stage5:
	cd lean && lake exe cache get && ./check_stage5.sh

lean-stage5b:
	cd lean && lake exe cache get && ./check_stage5b.sh

all: check lean-sync lean
