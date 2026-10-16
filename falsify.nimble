# Package

version       = "0.1.0"
author        = "Wally"
description   = "Property-based testing for Nim: falsify your properties"
license       = "MIT"
srcDir        = "src"

# Dependencies

requires "nim >= 2.0.0"

# Tasks

task test, "Run the self-tests":
  exec "nim c -r --hints:off --path:src tests/test_falsify.nim"
