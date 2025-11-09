{
  "targets": [
    {
      "target_name": "uor",
      "sources": [
        "src/uor_addon.cc",
        "../../ffi/c/minimal_wrapper.c"
      ],
      "include_dirs": [
        "<!@(node -p \"require('node-addon-api').include\")",
        "../../ffi/c"
      ],
      "defines": ["NAPI_DISABLE_CPP_EXCEPTIONS"],
      "cflags": ["-fPIC", "-O2"],
      "cflags_cc": ["-fPIC", "-O2", "-std=c++17"]
    }
  ]
}