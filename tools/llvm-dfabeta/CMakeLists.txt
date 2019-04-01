set(LLVM_LINK_COMPONENTS
  IRReader
  Core
  Support
  Slicer
  )

add_llvm_tool(llvm-dfabeta
  llvm-dfabeta.cpp
  )
