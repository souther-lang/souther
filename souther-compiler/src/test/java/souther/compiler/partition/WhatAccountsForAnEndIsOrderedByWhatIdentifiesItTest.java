package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Several conjuncts accounting for one end are answered in one order, and it is theirs.
 *
 * <p>Which is what a line is told apart by, so an order read off the walk that collected them would
 * make two readings of one edge into two lines. What identifies a clause is the declaration it is
 * written on and which of that declaration's clauses it is; what a report calls it holds neither
 * the module nor the ordinal.
 *
 * <p>Two modules each declaring a {@code Span} is where those two part. Their clauses print alike
 * and are two clauses, and a comparator on the printed name answers nought for them — which leaves
 * a stable sort holding whatever order the walk happened to collect them in.
 */
class WhatAccountsForAnEndIsOrderedByWhatIdentifiesItTest {

    /**
     * One number, and two clauses accounting for where it stops, on two declarations printing
     * alike.
     *
     * <p>The inner {@code Span} bounds the value below and the outer one takes the bound's own
     * value away, so the values start at one and both clauses hold them there. Each is the first
     * clause of its declaration and each is its clause's first conjunct, so nothing but the
     * declaration tells the two apart.
     */
    private static final String INNER = """
            module zzz exposing ( Span )

            data Span = Int
                invariant atLeastNought = value >= 0
            """;

    private static final String OUTER = """
            module aaa

            import zzz

            data Span = zzz.Span
                invariant notNought = value /= 0

            data Ok

            behavior take : (n: Span) -> Ok
            let take (n) = Ok
            """;

    /**
     * Both are answered, in the order their declarations are in.
     *
     * <p>{@code inner} before {@code outer}, which is what comparing the declarations gives and
     * what comparing the printed names cannot: both print {@code invariant Span}.
     */
    @Test
    void twoClausesPrintingAlikeAreOrderedByTheDeclarationsTheyAreWrittenOn() {
        assertEquals(List.of("aaa.Span", "zzz.Span"), declarationsAccountingForTheEnd(),
                "the declaration is what tells one clause from another, and the name is not");
    }

    /** Which declarations the borders at the end are owed to, in the order they are answered. */
    private static List<String> declarationsAccountingForTheEnd() {
        Compilation compilation = Compilation.ofSources(List.of(INNER, OUTER), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                Adequacy.boundariesOf(compilation.db(), "aaa");
        if (boundaries == null) {
            throw new AssertionError("the model under test compiles: "
                    + compilation.errors().stream()
                            .map(each -> each.diagnostic().code()).toList());
        }
        return boundaries.values().stream().flatMap(List::stream)
                .map(each -> declarationOf(each.origin()))
                .toList();
    }

    /** Which declaration drew the line, taken out of what the origin holds. */
    private static String declarationOf(LineOrigin origin) {
        if (!(origin instanceof LineOrigin.InvariantOrigin invariant)) {
            throw new AssertionError("this line was not drawn by an invariant: " + origin);
        }
        souther.compiler.types.TypeSymbol.AtModule on = invariant.rule().clause().id().declaredOn();
        return on.module() + "." + on.name();
    }
}
