package souther.compiler.check;

import souther.compiler.core.Core;

import java.util.List;

/**
 * What a reading may spend, in the two places it can spend without a bound.
 *
 * <p><b>How much of a declaration's clauses it may hold apart.</b> A choice between alternatives written at two positions is a union of products, and holding it
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
 * <p><b>How far from the point it will lay out a grid.</b> A divide rounded to a scale answers a
 * value of that scale's grid, and what a range says of it is the two points of that grid the exact
 * quotient lies between (spec §invariant-discharge-arithmetic). Laying one out costs a digit per
 * place, so a scale written large enough is a grid no reading should try to name — a million places
 * is a number a megabyte wide. A scale past the limit is a scale this reading has no grid for,
 * which is what a scale it cannot read as one number already is.
 *
 * <p>The two questions a scale raises are not one. What the run time takes is settled by the
 * language, which holds a scale to what can be handed over as the number it is and aborts outside
 * that (spec §stdlib-decimal); what a reading can lay out is settled here. A reading that asked
 * only the first would be one whose cost the source decides, and one that merged the two would put
 * a resource bound where a statement about the arithmetic belongs.
 *
 * <p><b>Owned by the compilation and not made here.</b> Nothing that reads a declaration decides
 * what it may be read with: a policy made where it is needed is one that can differ between two
 * readings of the same declaration, and the two would answer a position differently while each
 * stayed sound. So this arrives from the query graph, and the analysis takes it.
 */
public record ReadingPolicy(int dnfExpansionLimit, int scalePlacesLimit,
                            souther.compiler.regex.PatternPlan.Budget admittedValues) {

    public ReadingPolicy {
        // A reading builds machines to say what a position admits, and how much it may build is a
        // resource bound like the two above. Held here rather than picked up where the building
        // happens, so that what a declaration can be answered about exactly is the compilation's
        // and not a constant whichever reader got there first reached for.
        if (admittedValues == null) {
            throw new IllegalArgumentException("a reading is allowed something to build with");
        }
        // A guardrail is a positive number a count can be compared against, and a limit outside
        // that is one no reading is bounded by. Refused here rather than left to whoever writes it:
        // this is a resource bound, and a bound that admits everything is the absence of one.
        if (dnfExpansionLimit < 1) {
            throw new IllegalArgumentException(
                    "a reading holds at least one alternative, so a limit below one bounds nothing: "
                            + dnfExpansionLimit);
        }
        // Nought is a limit: a scale of nought is the whole numbers, which is a grid, and refusing
        // every other one is a reading that lays out only that. Below it is not a count of places.
        if (scalePlacesLimit < 0) {
            throw new IllegalArgumentException(
                    "a scale is a count of places from the point, so a limit below nought bounds"
                            + " nothing: " + scalePlacesLimit);
        }
    }

    /**
     * Whether a reading will lay out the grid a divide rounded to {@code places} answers on.
     *
     * <p>Either way from the point. A scale left of it rounds to hundreds and is as much a grid as
     * one that keeps two places, and a number a million places either way is as wide either way.
     */
    boolean laysOutAGridAt(int places) {
        return places >= -scalePlacesLimit && places <= scalePlacesLimit;
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

    /**
     * A fresh allowance for the positions of one answer, at what this compilation allows.
     *
     * <p>The allowance and not the number. What a reader here needs is somewhere to charge what it
     * builds, and every arrangement that makes when a question was asked no part of what it cost is
     * inside {@link souther.compiler.values.Allowance} — handed the figure instead, a reader could
     * make one of its own for each question it happened to ask, and a position would be allowed its
     * machine once per asker.
     *
     * @param <A> what a position is called
     */
    public <A> souther.compiler.values.Allowance<A> allowanceForAdmittedValues() {
        return souther.compiler.values.Allowance.of(admittedValues);
    }
}
