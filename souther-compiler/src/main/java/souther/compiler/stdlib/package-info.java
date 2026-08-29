/**
 * What the standard library declares, as a value.
 *
 * <p>Every operation the library ships, the signature each was resolved to, which names are sugar
 * for which, which kernels the library names, and the declarations the language itself gives. One
 * finished {@link souther.compiler.stdlib.Stdlib}, built once and never written again.
 *
 * <h2>Why it is not owned by the check that loads it</h2>
 *
 * <p>These lived in {@code check.Prelude}, whose static initializer parses the library's sources and
 * runs them through {@code Resolve} and {@code TypeOps}. That address made the coupling look
 * unbreakable — loading needs the check and the check reads what was loaded, so the dependency
 * appears to run both ways — but the cycle is between the reading and the loading, not between the
 * library and the check. Split apart, the direction is plain:
 *
 * <pre>
 *     Reserved  &lt;-  Stdlib  &lt;-  check.StdlibLoader  -&gt;  Resolve / TypeOps
 * </pre>
 *
 * <p>Only the loader reads both. So the library's declarations are answered from here, and code
 * generation and documentation read them without taking the whole of name resolution with them.
 *
 * <h2>What may not be said here</h2>
 *
 * <p><b>A fact about how a declaration is implemented never belongs to the library.</b> What
 * {@code Decimal.round} means — its parameters, what it answers, the kernel key behind it — is the
 * library's. Which JVM class {@code RoundingMode} is, what descriptor a kernel is invoked with,
 * whether a language-declared type is shipped by hand or generated: each is one backend's answer to
 * a question another backend answers differently, and each belongs to that backend.
 *
 * <p>The line is drawn by what the fact is about and not by how many things read it. So this package
 * depends on the language — {@link souther.compiler.Reserved}, {@link souther.compiler.ast.Hir},
 * {@link souther.compiler.types} — and on nothing that reads it. Neither {@code check} nor
 * {@code codegen} nor {@code jvm} may be named from here, and a test holds it.
 */
package souther.compiler.stdlib;
