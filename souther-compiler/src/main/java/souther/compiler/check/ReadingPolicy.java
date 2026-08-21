package souther.compiler.check;

import souther.compiler.core.Core;

import java.util.List;

/**
 * How much of a declaration's clauses a reading may hold apart.
 *
 * <p>A choice between alternatives written at two positions is a union of products, and holding it
 * is what lets the next conjunction answer each position exactly. What it costs is one alternative
 * per branch, multiplied through every conjunction — so a clause written to expand far enough is
 * one no reading should try, and the reading falls back to merging the alternatives into the one
 * product containing them.
 *
 * <p><b>A guardrail and not a precision setting.</b> Measured over the compiler's own suite —
 * 68,725 readings, 42,377 clauses — the largest expansion any clause reaches is five, and 98.97% of
 * clauses reach one; over the bench corpus, which is whole applications, every clause reaches one.
 * So nothing written here is read by the fallback at any limit of eight or more. What the design
 * needs is that a finite limit exists; which one a compilation sets is the compilation's, and is
 * written where a reading cannot reach it.
 *
 * <p><b>Owned by the compilation and not made here.</b> Nothing that reads a declaration decides
 * what it may be read with: a policy made where it is needed is one that can differ between two
 * readings of the same declaration, and the two would answer a position differently while each
 * stayed sound. So this arrives from the query graph, and the analysis takes it.
 */
public record ReadingPolicy(int dnfExpansionLimit) {

    public ReadingPolicy {
        // A guardrail is a positive number a count can be compared against, and a limit outside
        // that is one no reading is bounded by. Refused here rather than left to whoever writes it:
        // this is a resource bound, and a bound that admits everything is the absence of one.
        if (dnfExpansionLimit < 1) {
            throw new IllegalArgumentException(
                    "a reading holds at least one alternative, so a limit below one bounds nothing: "
                            + dnfExpansionLimit);
        }
    }

    /**
     * How many alternatives the clauses of one declaration would expand to, counted before any of
     * them is read.
     *
     * <p>Asked of the whole declaration and before any of it is read. Its clauses are met, so what
     * they expand to together is the product of what each expands to, and a bound on that bounds
     * every step of the fold: every partial product is at most the whole, and inside a clause the
     * cost of a part is at most the cost of the clause. So a declaration admitted here cannot
     * exceed the limit part way through, and no second control during the fold is needed.
     *
     * <p>Per declaration rather than per clause. Deciding per clause would let an unrelated clause
     * added beside an existing one change how that one is read, and over this repository it buys
     * nothing: no declaration of it exceeds any usable limit.
     */
    long expansionOf(List<Core> clauses) {
        return ExpansionCost.of(clauses, dnfExpansionLimit);
    }

    /** Whether a declaration that expands to {@code cost} alternatives may hold them apart. */
    boolean holdsApart(long cost) {
        return cost <= dnfExpansionLimit;
    }
}
