clang -S -g -emit-llvm example.c  -fno-exceptions -Xclang -disable-O0-optnone
opt -load-pass-plugin=target/debug/libplimmix_plugin_shared.dylib   -passes="plimmix,function(replace-malloc),rewrite-statepoints-for-gc" -o example_opt.ll -S example.ll
clang -fplugin=target/debug/libplimmix_plugin_shared.dylib test_.ll target/debug/libimmix.a 
