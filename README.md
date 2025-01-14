# Immix GC for LLVM-based Languages

Welcome to the Immix GC project! This project aims to provide a highly efficient and easily integrable [immix garbage collector (GC)][2] for all languages that use LLVM as their backend. Originally a part of the [Pivot Lang project](https://github.com/Pivot-Studio/pivot-lang), this GC leverages LLVM's [stackmap][1] functionality to assist in stack scanning and supports both conservative and precise garbage collection.

[1]: https://llvm.org/docs/StackMaps.html
[2]: https://www.steveblackburn.org/pubs/papers/immix-pldi-2008.pdf

## Features

- **High Performance**: Designed for high efficiency to minimize the overhead of garbage collection.
- **Easy Integration**: Simple to integrate with any LLVM-based language.
- **Support for Conservative and Precise Collection**: Flexible enough to work with both conservative and precise memory management paradigms.
- **LLVM Stackmap Integration**: Utilizes LLVM's stackmap feature for effective stack scanning.
- **LLVM Passes and GC Strategy Plugins**: Comes with built-in LLVM passes and corresponding GC strategy plugins to facilitate integration.
- **Evacuation**: Supports object evacuation to reduce fragmentation and improve memory locality.

## Supported Platforms

- Linux amd64
- windows amd64
- macOS aarch64

The above 3 platforms are tested and supported, other platforms may work but are not officially supported.

Theoretically this GC should work on all amd64 and aarch64 platforms.

## Build

To build the Immix GC, you will need to have the following dependencies installed:

- LLVM 18.x
- CMake 3.10 or higher
- Rust 1.55 or higher

Once you have the dependencies installed, you can build the Immix GC by following these steps:

1. Clone the repository:
2. Build project with Cargo:

    ```bash
    cargo build
    ```

    don't forget to add the `--release` flag if you want to build the release version.

## Some important notes

Current GC's allocation fast path is implemented in raw LLVM IR, it only fallbacks to Rust allocation
routine when 1. the allocation size is too large or 2. the current 'hole' is not large enough to hold the object.

The GC algorithm **requires the allocated memory to be zeroed or initialized before next possible GC cycle**,
this is because the reused memory may contain object headers dead in previous GC cycles, which may
leading to finding wrong object header during collection.

So if you are using the GC apart from the 'LLVM IR fast path', you should always zero or initialize the allocated memory just after allocation.

By the way, the LLVM IR fast path is implemented in `alloc-*.ll` files.

## Usage

### Using Immix GC on C Programs

TODO

## Release Notes

### v0.2.0

- Rewrote the allocation and collection logic to improve performance.
- Reimplement fast allocation path in raw LLVM IR to make the allocation process as fast as possible.
- Imporve the escape analysis to reduce the number of objects that need to be allocated on the heap.

TODO: Update usage docs

### v0.1.0

- Initial release of the Immix GC project.

## Language using Immix GC

- [Pivot Lang](https://github.com/Pivot-Studio/pivot-lang)

## Contributing

We welcome contributions from the community! Here are some ways you can contribute:

- Submit bug reports and feature requests.
- Write documentation and tutorials.
- Improve the performance and capabilities of the GC.
- Integrate Immix GC with more languages and provide examples.

## License

This project is licensed under the MIT License. See the [LICENSE](LICENSE) file for more details.

## Acknowledgements

This project is inspired by the need for a performant garbage collection system in the [Pivot Lang project](https://github.com/Pivot-Studio/pivot-lang) and has evolved to become a stand-alone solution for all LLVM-based languages. Special thanks to all contributors and the LLVM community for their support.

---

Happy Coding!
