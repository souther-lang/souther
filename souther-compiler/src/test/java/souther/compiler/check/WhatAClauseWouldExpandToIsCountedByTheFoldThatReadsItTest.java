package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.CoverageOrigin;
import souther.compiler.types.Type;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * How many alternatives a clause would come to, counted before any of them is built.
 *
 * <p>A budget has to be measurable before the work it limits. The number of alternatives a clause
 * comes to once duplicates are gone is not: finding it out is the expansion this is asked to bound.
 * So what is counted is the syntax — a choice adds, a conjunction multiplies, and a denial swaps the
 * two.
 *
 * <p><b>Counted on the fold that does the reading.</b> Which shapes are connectives, where a denial
 * goes and what is left as a leaf are {@link ClauseReading}'s. A walk of its own saying the same
 * thing again is a second answer that agrees with the first only until somebody changes one of
 * them — and the two coming apart is not a wrong count, it is a reading that expands past the
 * budget admitted for it.
 */
class WhatAClauseWouldExpandToIsCountedByTheFoldThatReadsItTest {

    private static final SourcePos POS = new SourcePos(0, 0);

    /** What is a leaf is the fold's answer and not this test's: anything with no connective on top
     *  of it costs one, whatever a reading later makes of it. */
    private static Core leaf() {
        return new Core.Bool(true, Type.BOOL, POS);
    }

    private static Core and(Core left, Core right) {
        return new Core.Binary(Hir.BinOp.AND, left, right, CoverageOrigin.unwritten(), Type.BOOL,
                POS);
    }

    private static Core or(Core left, Core right) {
        return new Core.Binary(Hir.BinOp.OR, left, right, CoverageOrigin.unwritten(), Type.BOOL,
                POS);
    }

    /** As the analysis representation spells one, which is what {@link Predicates#negated} reads. */
    private static Core not(Core e) {
        return new Core.If(e, new Core.Bool(false, Type.BOOL, POS),
                new Core.Bool(true, Type.BOOL, POS), CoverageOrigin.unwritten(), Type.BOOL, POS);
    }

    private static int cost(Core e) {
        return new ExpansionCost(64).read(e, true);
    }

    @Test
    void aClauseOfNoConnectiveIsOneAlternative() {
        assertEquals(1, cost(leaf()));
    }

    @Test
    void aChoiceAddsAndAConjunctionMultiplies() {
        assertEquals(2, cost(or(leaf(), leaf())));
        assertEquals(1, cost(and(leaf(), leaf())));
        assertEquals(4, cost(and(or(leaf(), leaf()), or(leaf(), leaf()))));
    }

    /**
     * A denial swaps them, because that is what it does to the connectives it is carried through.
     *
     * <p>Not stated here twice. The fold carries a denial down to the leaves, so the count of a
     * denied clause is the count of the clause read denied — which is the law, and the two arms
     * above are what it comes to.
     */
    @Test
    void aDenialCountsWhatTheClauseUnderItCountsDenied() {
        for (Core each : List.of(leaf(), or(leaf(), leaf()), and(leaf(), leaf()),
                and(or(leaf(), leaf()), leaf()), or(and(leaf(), leaf()), leaf()))) {
            assertEquals(new ExpansionCost(64).read(each, false), cost(not(each)),
                    "a denial is carried down and not applied to what a branch came to");
        }
        assertEquals(1, cost(not(or(leaf(), leaf()))), "a denied choice is a conjunction");
        assertEquals(2, cost(not(and(leaf(), leaf()))), "and a denied conjunction is a choice");
    }

    /**
     * The count follows the connectives and not the brackets.
     *
     * <p>Which is what lets the domain be chosen before the fold: a declaration written one way and
     * the same declaration written another are admitted alike, so precision cannot turn on how an
     * author bracketed a choice.
     */
    @Test
    void theCountDoesNotFollowTheBracketsOrTheOrder() {
        Core left = or(or(leaf(), leaf()), leaf());
        Core right = or(leaf(), or(leaf(), leaf()));

        assertEquals(3, cost(left));
        assertEquals(3, cost(right));
        assertEquals(cost(and(left, right)), cost(and(right, left)));
    }

    /** A declaration is its clauses met, so what it costs is their product. */
    @Test
    void aDeclarationCostsTheProductOfItsClauses() {
        assertEquals(6, ExpansionCost.of(List.of(or(leaf(), leaf()),
                or(or(leaf(), leaf()), leaf())), 64));
        assertEquals(1, ExpansionCost.of(List.of(), 64), "and nothing read costs one");
    }

    /**
     * A count that runs past the limit stops there rather than overflowing.
     *
     * <p>What is asked of it is whether the limit is exceeded, and past that the number is not
     * wanted. Left to run, a conjunction of choices is a product that leaves the range of the
     * count's own type long before it leaves the range of what an author can write.
     */
    @Test
    void aCountThatRunsPastTheLimitSaturates() {
        Core deep = leaf();
        for (int i = 0; i < 64; i++) {
            deep = and(or(leaf(), leaf()), deep);
        }

        assertEquals(65, cost(deep), "saturated at one past the limit, and not overflowed");
        assertEquals(4, new ExpansionCost(3).read(and(or(leaf(), leaf()), or(leaf(), leaf())), true),
                "a limit of its own is saturated at one past that");
    }
}
