PYTHON ?= python3
.PHONY: check certs logic explicit lean lean-sync all

# One command: the certificates and the brute-force logic checks (pure standard-library Python, one core,
# well under 1 GB; about 4 minutes). Each script exits 0 only on PASS, and the certificate output is compared
# with the committed transcript.
check: certs logic explicit

certs:
	cd cert && $(PYTHON) cert_gamma.py | cmp - cert_gamma.out && $(PYTHON) cert_eps.py | cmp - cert_eps.out
	@echo "certificates: PASS"

logic:
	cd cert && $(PYTHON) check_stage1.py > /dev/null && $(PYTHON) check_stage2.py > /dev/null
	cd PROOF/ye-li-audit && for f in yl_*.py; do $(PYTHON) $$f > /dev/null || exit 1; done
	@echo "logic checks: PASS"

# Stage 2b (explicit): the certificate against its transcript, and the gate-level toy test of Lemmas E1 to E4
# at N = 8 (about 30 s, about 200 MB).
explicit:
	cd cert && $(PYTHON) cert_explicit.py | cmp - cert_explicit.out && $(PYTHON) toy_explicit.py > /dev/null
	@echo "explicit (Stage 2b) certificate and toy test: PASS"

# The generated Lean point files must be exactly what the generators produce from cert/.
lean-sync:
	cd lean && $(PYTHON) gen_stage1.py > /dev/null && $(PYTHON) gen_stage2.py > /dev/null \
		&& $(PYTHON) gen_explicit.py > /dev/null
	git diff --exit-code -- lean/SubsetsumLean && echo "lean sources in sync with cert/: PASS"

# Lean 4 kernel check (lean/LEAN_SCOPE.md). Needs elan with Lean v4.34.1; fetches prebuilt Mathlib oleans
# (about 7 GB on disk), never compiles Mathlib. About 2 minutes; peak RSS below 3 GB (build_watch.sh aborts above).
# Every printed theorem must depend only on propext, Classical.choice and Quot.sound (or a subset of them); the
# Stage 2b theorems (Explicit.lean) must be among them.
AX := (propext|Classical\.choice|Quot\.sound)
lean:
	cd lean && lake exe cache get && ./build_watch.sh build \
		&& ./build_watch.sh env lean SubsetsumLean/Axioms.lean > axioms.check \
		&& test $$(grep -cE "depends on axioms: \[$(AX)(, $(AX))*\]$$" axioms.check) -eq \
			$$(grep -c '^#print axioms' SubsetsumLean/Axioms.lean) \
		&& grep -q "'SS.explicit_A' depends on axioms" axioms.check \
		&& test $$(grep -c "'SS.explicit_" axioms.check) -eq 13 \
		&& echo "lean: PASS (standard axioms only; Stage 2b explicit certificate included)"

all: check lean-sync lean
