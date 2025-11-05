{
  "targets": [
    {
      "target_name": "uor_runtime",
      "sources": [
        "src/uor_runtime.cc",
        "../../ffi/c/minimal_wrapper.c"
      ],
      "include_dirs": [
        "<!@(node -p \"require('node-addon-api').include\")",
        "../../ffi/c"
      ],
      "dependencies": [
        "<!(node -p \"require('node-addon-api').gyp\")"
      ],
      "cflags": ["-fPIC"],
      "cflags_cc": ["-fPIC", "-std=c++17"],
      "defines": ["NAPI_DISABLE_CPP_EXCEPTIONS"],
      "conditions": [
        ["OS=='win'", {
          "defines": ["_HAS_EXCEPTIONS=1"]
        }]
      ]
    }
  ]
}