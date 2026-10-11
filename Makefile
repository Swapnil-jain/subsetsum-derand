PYTHON ?= python3
.PHONY: check certs logic explicit stage3 lean lean-sync all

# One command: the certificates and the brute-force logic checks (pure standard-library Python, one core,
# well under 1 GB; about 4 minutes). Each script exits 0 only on PASS, and the certificate output is compared
# with the committed transcript.
check: certs logic explicit stage3

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

# The generated Lean point files must be exactly what the generators produce from certificates/.
lean-sync:
	cd lean && $(PYTHON) gen_stage1.py > /dev/null && $(PYTHON) gen_stage2.py > /dev/null \
		&& $(PYTHON) gen_explicit.py > /dev/null && $(PYTHON) gen_stage3.py > /dev/null && $(PYTHON) gen_explicit_n0.py > /dev/null
	git diff --exit-code -- lean/SubsetsumLean && echo "lean sources in sync with certificates/: PASS"

# Lean 4 kernel check (lean/LEAN_SCOPE.md). Needs elan with Lean v4.34.1; fetches prebuilt Mathlib oleans
# (about 7 GB on disk), never compiles Mathlib. About 4 minutes; peak RSS below 3 GB (build_watch.sh aborts above).
# Every printed theorem must depend only on propext, Classical.choice and Quot.sound (or a subset of them); the
# Stage 2b theorems (Explicit.lean) and the 42 smaller-n0 theorems of Secs. 12-13 (namespace SS.N0) must be among
# them.
AX := (propext|Classical\.choice|Quot\.sound)
lean:
	cd lean && lake exe cache get && ./build_watch.sh build \
		&& ./build_watch.sh env lean SubsetsumLean/Axioms.lean > axioms.check \
		&& test $$(grep -cE "depends on axioms: \[$(AX)(, $(AX))*\]$$" axioms.check) -eq \
			$$(grep -c '^#print axioms' SubsetsumLean/Axioms.lean) \
		&& grep -q "'SS.explicit_A' depends on axioms" axioms.check \
		&& test $$(grep -c "'SS.explicit_" axioms.check) -eq 13 \
		&& test $$(grep -c "'SS.s3_" axioms.check) -eq 34 && grep -q "'SS.s3_E3' depends" axioms.check \
		&& test $$(grep -c "'SS.N0\." axioms.check) -eq 42 \
		&& echo "lean: PASS (standard axioms only; Stage 2b certificates, Secs. 12-13 and Stage 3 included)"

all: check lean-sync lean
