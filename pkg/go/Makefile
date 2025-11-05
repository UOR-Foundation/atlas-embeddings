# Makefile for Go UOR FFI bindings

.PHONY: all test bench clean install

all: test

test:
	cd src && go test -v

bench:
	cd src && go test -bench=. -benchmem

clean:
	cd src && go clean -cache -testcache

install:
	cd src && go install

fmt:
	cd src && go fmt ./...

vet:
	cd src && go vet ./...

coverage:
	cd src && go test -coverprofile=coverage.out
	cd src && go tool cover -html=coverage.out -o coverage.html