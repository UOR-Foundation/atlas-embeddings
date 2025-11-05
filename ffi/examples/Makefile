# Examples Makefile

CC = gcc
CFLAGS = -O2 -g -I../c
EXAMPLES = simple advanced

.PHONY: all clean

all: $(EXAMPLES)

simple: simple.c
	$(CC) $(CFLAGS) -o $@ $<
	@echo "Built: $@"

advanced: advanced.c
	$(CC) $(CFLAGS) -o $@ $<
	@echo "Built: $@"

run: all
	@echo "=== Running Simple Example ==="
	./simple
	@echo ""
	@if [ -f ./advanced ]; then \
		echo "=== Running Advanced Example ==="; \
		./advanced; \
	fi

clean:
	rm -f $(EXAMPLES)
	@echo "Examples cleaned"