# Hologramapp Documentation

This directory contains technical documentation for the hologramapp project.

## Architecture & Design

### [Backend Architecture](./BACKEND_ARCHITECTURE.md)
**Essential reading for backend development**

Comprehensive explanation of the backend architecture design, including:
- Why `instruction_ops` are free functions vs trait methods
- Performance analysis and tradeoffs
- Guidelines for implementing new backends (GPU, TPU, FPGA)
- Testing strategies
- Clear separation between backend-specific and shared operations

**Key takeaway**: The current design achieves optimal performance and maintainability by keeping shared instructions as free functions and only backend-specific operations as trait methods.

### [Backend Trait Architecture](./BACKEND_TRAIT_ARCHITECTURE.md)
Documentation of the two-trait architecture:
- `Backend` trait: Public API (buffer/pool management, program execution)
- `Executor` trait: Internal execution interface (instruction dispatch, synchronization)

Created during the refactoring that moved all execution logic into the `CpuExecutor` struct.

### [CPU Backend Tracing](./CPU_BACKEND_TRACING.md)
Comprehensive guide to the tracing instrumentation added to the CPU backend:
- How to enable and configure tracing
- Performance impact analysis
- Example output and usage
- Environment variables for configuration
- Integration with `hologram-tracing` crate

## Sigmatics

### [Sigmatics Guide](./SIGMATICS_GUIDE.md)
User guide for the Sigmatics canonicalization engine:
- Circuit compiler usage
- Pattern-based canonicalization
- 96-class geometric system
- Generator operations
- Transform algebra

### [Sigmatics Implementation Review](./SIGMATICS_IMPLEMENTATION_REVIEW.md)
Technical implementation details:
- AST structure
- Parser design
- Rewrite engine
- Canonicalization algorithms
- Performance characteristics

## Future Work

### [Future Prompts](./FUTURE_PROMPTS.md)
**Development roadmap and task queue**

Contains planned features and improvements:
- Move Sigmatics compilation from runtime to compile-time
- Implement GPU backend
- Implement TPU backend
- Backend auto-selection
- And more...

This document serves as the task backlog for the project.

## Project Guidelines

See [../CLAUDE.md](../CLAUDE.md) for:
- Development workflow
- Code organization standards
- Testing requirements
- Documentation standards
- Common patterns and best practices

## Contributing

When adding new documentation:
1. Place `.md` files in the `/docs` directory
2. Add entry to this README with brief description
3. Update references in [CLAUDE.md](../CLAUDE.md)
4. Use clear headers and table of contents for long documents
5. Include code examples where appropriate

## Quick Links

### By Topic

**Backend Development**:
- [Backend Architecture](./BACKEND_ARCHITECTURE.md) - Design decisions
- [Backend Trait Architecture](./BACKEND_TRAIT_ARCHITECTURE.md) - Trait design
- [CPU Backend Tracing](./CPU_BACKEND_TRACING.md) - Performance monitoring

**Sigmatics**:
- [Sigmatics Guide](./SIGMATICS_GUIDE.md) - User guide
- [Sigmatics Implementation](./SIGMATICS_IMPLEMENTATION_REVIEW.md) - Technical details

**Planning**:
- [Future Prompts](./FUTURE_PROMPTS.md) - Roadmap and task queue

### By Audience

**New Contributors**:
1. Start with [CLAUDE.md](../CLAUDE.md) - Development guidelines
2. Read [Backend Architecture](./BACKEND_ARCHITECTURE.md) - System design
3. Review [Sigmatics Guide](./SIGMATICS_GUIDE.md) - Core concepts

**Backend Implementers** (GPU, TPU, etc.):
1. [Backend Architecture](./BACKEND_ARCHITECTURE.md) - **Must read**
2. [Backend Trait Architecture](./BACKEND_TRAIT_ARCHITECTURE.md)
3. [CPU Backend Tracing](./CPU_BACKEND_TRACING.md) - Add tracing to your backend

**Performance Engineers**:
1. [CPU Backend Tracing](./CPU_BACKEND_TRACING.md) - Monitoring tools
2. [Backend Architecture](./BACKEND_ARCHITECTURE.md) - Performance analysis
3. [Sigmatics Guide](./SIGMATICS_GUIDE.md) - Canonicalization optimization

## Document Status

| Document | Status | Last Updated | Maintenance |
|----------|--------|--------------|-------------|
| [Backend Architecture](./BACKEND_ARCHITECTURE.md) | ✅ Current | 2025-10-28 | Update when adding new backends |
| [Backend Trait Architecture](./BACKEND_TRAIT_ARCHITECTURE.md) | ✅ Current | 2024-12 | Update if trait design changes |
| [CPU Backend Tracing](./CPU_BACKEND_TRACING.md) | ✅ Current | 2025-10-28 | Update when adding new metrics |
| [Sigmatics Guide](./SIGMATICS_GUIDE.md) | ✅ Current | 2024 | Update with new features |
| [Sigmatics Implementation](./SIGMATICS_IMPLEMENTATION_REVIEW.md) | ✅ Current | 2024 | Update with major changes |
| [Future Prompts](./FUTURE_PROMPTS.md) | 🔄 Living Document | Ongoing | Update as tasks complete |

---

**Note**: All documentation follows the project standard that `.md` files belong in `/docs`, with two exceptions:
- `README.md` - Project overview at repository root
- `CLAUDE.md` - Development guide at repository root
