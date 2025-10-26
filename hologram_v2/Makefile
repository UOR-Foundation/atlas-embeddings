.PHONY: lint unit property acceptance liveness receipts gate docs quickstarts

lint:
@echo "lint stub"

unit:
@python -m pytest -q tests/unit || true

property:
@python -m pytest -q tests/property || true

acceptance:
@python -m pytest -q tests/acceptance || true

liveness:
@python -m pytest -q tests/liveness || true

receipts:
@echo "receipts stub"

gate: acceptance
@echo "gate stub"

docs:
@echo "docs stub"

quickstarts:
@echo "quickstarts stub"
