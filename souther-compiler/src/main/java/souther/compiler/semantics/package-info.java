/**
 * What the language's own operations are, as propositions about the operations.
 *
 * <p>Nothing here is about a reader. What {@code Date.daysBetween} answers, that
 * {@code Int.abs} is never negative, that {@code Date.addMonths} moves a date by no
 * fixed number of days: each is true of the operation whether or not anything in this
 * compiler asks. This package holds those, once, and the checks that hold each of them
 * to the declaration it was written for.
 *
 * <h2>Why it is not owned by whoever asks first</h2>
 *
 * <p>These lived in the invariant-discharge check, which is one of the things that reads
 * them. The arrangement works until a second reader needs one, and then the fact is
 * promoted to somewhere both can see — which is what {@link
 * souther.compiler.check.NumericMeasures} was, and its own comment records what the
 * promotion was for: two lists of the same operations disagreed, and a rule discharged in
 * one place was reported in the other as a rule the model does not state.
 *
 * <p>Promoting on the second reader leaves the structure that produced it. A fact still
 * arrives in whichever consumer needed it first, and is still moved out later by whoever
 * needed it second, so the same repair is owed again every time. What removes the repair
 * is the ownership rule, held from the first reader rather than the second:
 *
 * <p><b>An intrinsic fact about an operation never belongs to a consumer.</b> A
 * proposition true of the operation is declared here. A rule about what a procedure does
 * with such a proposition — which of them it enforces, what it reports when it cannot —
 * belongs to that procedure.
 *
 * <p>The line is drawn by what the proposition is about and not by how many things read
 * it. "{@code List.filter} answers some of the elements it was given" is about the
 * operation, and is declared here on the day one reader wants it. "A clause over a
 * container is discharged where the predicate survives the construction" is about the
 * discharge procedure, and stays there.
 *
 * <h2>The dependency direction</h2>
 *
 * <p>This package depends on the language — {@link souther.compiler.core.Core}, {@link
 * souther.compiler.types}, the numeric domain — and on nothing that reads it. Neither
 * {@code check} nor {@code partition} may be named from here, and a test holds it: a fact
 * that reached back into a reader would be a fact written for that reader, which is the
 * arrangement this package exists to end.
 */
package souther.compiler.semantics;
