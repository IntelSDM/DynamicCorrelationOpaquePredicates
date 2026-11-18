# Dynamic Correlation Opaque Predicates
Built for LLVM 19.1 - Windows x64 <br> <br>

We can take preexisting conditions where there is an unknown, correlate the unknown value to then use a known value to do an impossible comparison. So not all cases are false, they will be real and fake ones. Just we just utilize the preexisting real unknown value to stem our impossible inverse off of the dynamic unknown. <br>
Since it is dependent on a pre existing unknown input, it is entirely dynamic, forcing dynamic analysis. Breaking SMT,Symbolic Execution, AI and the rest. <br>

## Annotations
```c
__attribute__((annotate("obfus")))
``` 
* Marks your function for the pass

## How To Build
* Download [LLVM 19.1](https://github.com/llvm/llvm-project/releases/tag/llvmorg-19.1.0)
* Download [VCPKG](https://github.com/microsoft/vcpkg)
* VCPKG install asmjit
* Open build.bat in a text editor.
* Find the LLVM 19.1 references in the command line, Change them to your file path.
* Find the VCPKG references in the command line, Change them to your file path.
* Run the build script
* Build your application with the ``` -load-pass-plugin ``` Param to the FunctionPass.dll
