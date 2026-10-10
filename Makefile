PYTHON ?= python3
.PHONY: check certs logic lean lean-sync all

# One command: the certificates and the brute-force logic checks (pure standard-library Python, one core,
# well under 1 GB; about 2.5 minutes). Each script exits 0 only on PASS, and the certificate output is compared
# with the committed transcript.
check: certs logic

certs:
	cd cert && $(PYTHON) cert_gamma.py | cmp - cert_gamma.out && $(PYTHON) cert_eps.py | cmp - cert_eps.out
	@echo "certificates: PASS"

logic:
	cd cert && $(PYTHON) check_stage1.py > /dev/null && $(PYTHON) check_stage2.py > /dev/null
	cd PROOF/ye-li-audit && for f in yl_*.py; do $(PYTHON) $$f > /dev/null || exit 1; done
	@echo "logic checks: PASS"

# The generated Lean point files must be exactly what the generators produce from cert/.
lean-sync:
	cd lean && $(PYTHON) gen_stage1.py > /dev/null && $(PYTHON) gen_stage2.py > /dev/null
	git diff --exit-code -- lean/SubsetsumLean && echo "lean sources in sync with cert/: PASS"

# Lean 4 kernel check (lean/LEAN_SCOPE.md). Needs elan with Lean v4.34.1; fetches prebuilt Mathlib oleans
# (about 7 GB on disk), never compiles Mathlib. About 2 minutes; peak RSS below 3 GB (build_watch.sh aborts above).
lean:
	cd lean && lake exe cache get && ./build_watch.sh build \
		&& ./build_watch.sh env lean SubsetsumLean/Axioms.lean > axioms.check \
		&& test $$(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' axioms.check) -eq \
			$$(grep -c '^#print axioms' SubsetsumLean/Axioms.lean) && echo "lean: PASS (standard axioms only)"

all: check lean-sync lean
