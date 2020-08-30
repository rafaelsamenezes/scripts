if(${LLVM_PACKAGE_VERSION} VERSION_LESS "7")
add_llvm_loadable_module(LLVMPassname
        Pass.cpp)
else()
    add_llvm_library(LLVMPassname MODULE
            Pass.cpp)
endif()

# Hack for Darwin
target_link_libraries(LLVMPassname
        "$<$<PLATFORM_ID:Darwin>:-undefined dynamic_lookup>")