/**
 * Compiler-side access to the classes a compilation emitted.
 *
 * <p>Three things a caller needs to reach generated code, and nothing else: {@link
 * souther.compiler.generated.MemoryClassLoader} makes a compilation's bytes into classes,
 * {@link souther.compiler.generated.JsonBoundary} reads and writes values across their derived
 * codecs, and {@link souther.compiler.generated.GeneratedBehavior} enters one. What they have in
 * common is the generated artifact, not a phase — none of this is codegen, or the query layer, or
 * the command line.
 *
 * <p>Every class here is {@code public} because its callers are in other modules of this repository:
 * souther-cli drives a behavior, and souther-bench loads what it measures. <strong>That does not
 * make any of it a supported API.</strong> Embedding the compiler from outside this repository goes
 * through {@link souther.compiler.Compiler}, which is the one class name a caller out there is meant
 * to write down; these carry no compatibility promise and their names may move.
 *
 * <p>Naming, since {@code generated} could be read two ways: it is what these classes are about, not
 * what they are. Nothing in this package is generated.
 */
package souther.compiler.generated;
