package souther.compiler.diag;

/**
 * A failure that says the compiler's own model contradicts itself, as opposed to one that says the
 * compiler could not follow a program.
 *
 * <p>An analysis that falls open swallows the second and must not swallow the first. A shape a walk
 * has no rule for is what falling open is for: the run-time check stands, and a limit of an analysis
 * can never reject a valid program. This is the other one — one name given two values, one clause
 * given two answers, a region running between two sources. Swallowed, it produces a subject with no
 * findings, which is exactly what a subject that passed produces, so the difference between "this
 * could not be analysed" and "this is proven" stops being readable anywhere.
 *
 * <p>What a boundary asks about is this type, rather than a list of the ones it knows of. A list is
 * a copy of this file kept somewhere else, and the way it goes wrong is silent: a compiler that
 * gains a new way to disagree with itself starts reporting that disagreement as an ordinary limit,
 * and nothing fails while it does.
 *
 * <p>An interface and not a class, and here rather than beside the check, because the two layers
 * that raise one cannot share a superclass: a place that is not a place is refused where regions
 * become places, and the readings of a clause are compared where clauses are read.
 */
public interface TheCompilerDisagreesWithItself {
}
