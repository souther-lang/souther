package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * Numbers fixed under two cases of one sum are fixed in no row.
 *
 * <p>A position holds one value, so a value that is an {@code A} is not also a {@code B}, and a
 * caller that put a number under each of them has asked about a row nothing can write. The rules
 * were never consulted: what contradicts is the pair of assignments, which is what tells this from
 * an input the declarations refuse.
 *
 * <p><b>And the answer does not carry the order the fixings arrived in.</b> Two of them said either
 * way round are the same two, so which position a refusal names, and which two narrowings it names
 * there, are settled by the model rather than by which question the caller asked first.
 */
class NoRowIsTwoCasesOfOneSumTest {

    private static final String MODEL = """
            module g

            data Shared = { lo: Int, hi: Int }
            data A = { ...Shared, x: Int }
            data B = { ...Shared, y: Int }
            data Q = A | B

            data Holder = { q: Q }

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    @Test
    void twoCasesFixedAtOncePutTheRowNowhere() {
        EmptyInput.TwoRefinementsAtOnePosition why = bothFixed(false);

        assertEquals("h.q", why.at().toString(), "the position that cannot be both");
        assertEquals("A", why.one().spelled());
        assertEquals("B", why.other().spelled());
    }

    @Test
    void andTheOrderTheyWereFixedInIsNoPartOfTheAnswer() {
        assertEquals(bothFixed(false), bothFixed(true),
                "the same two fixings, whichever way round they were said");
    }

    /**
     * A relation over a number under the other case, taken into a region that fixed one under the
     * first, is a condition no row meets, as the second fixing is: the region holds nothing, and
     * for the same reason.
     *
     * <p>Which is what a reader asking whether some element can meet two relations is told. Some
     * element of a list of a sum being an {@code A} with one number and a {@code B} with another is
     * no element, and the reader narrowing a region one relation at a time is how it finds that out.
     */
    @Test
    void aRelationTakenInUnderTheOtherCaseLeavesTheRowNowhere() {
        InputDomain read = reading(MODEL, "read");
        NumericTerm underA = new NumericTerm.ValueOf(pathOf(read, "h.q@A.lo"));
        NumericTerm underB = new NumericTerm.ValueOf(pathOf(read, "h.q@B.lo"));
        SearchRegion fixedUnderA = read.quantities(rulesOf(MODEL))
                .given(underA, Count.of(BigDecimal.ONE)).region();

        SearchRegion both = fixedUnderA.assuming(LinearForm.atom(underB), Rel.GE).taken();

        assertInstanceOf(EmptyInput.TwoRefinementsAtOnePosition.class,
                both.emptiness().orElseThrow(() -> new AssertionError(
                        "no row is both cases, and nothing said so")));
    }

    /** And a question about where a number under the other case runs, in that region, is
     *  answered: no row gives it a value there, so it runs nowhere. */
    @Test
    void aNumberUnderTheOtherCaseRunsNowhere() {
        InputDomain read = reading(MODEL, "read");
        NumericTerm underA = new NumericTerm.ValueOf(pathOf(read, "h.q@A.lo"));
        NumericTerm underB = new NumericTerm.ValueOf(pathOf(read, "h.q@B.lo"));
        SearchRegion fixedUnderA = read.quantities(rulesOf(MODEL))
                .given(underA, Count.of(BigDecimal.ONE)).region();

        assertInstanceOf(NumericDomain.FormProjection.NothingIsLeft.class,
                fixedUnderA.projectionOf(underB));
    }

    /** Both positions fixed, in one order or the other. */
    private static EmptyInput.TwoRefinementsAtOnePosition bothFixed(boolean reversed) {
        InputDomain read = reading(MODEL, "read");
        NumericTerm underA = new NumericTerm.ValueOf(pathOf(read, "h.q@A.lo"));
        NumericTerm underB = new NumericTerm.ValueOf(pathOf(read, "h.q@B.lo"));
        Quantities asked = read.quantities(rulesOf(MODEL));
        Optional<EmptyInput> why = (reversed
                ? asked.given(underB, Count.of(BigDecimal.TWO))
                        .given(underA, Count.of(BigDecimal.ONE))
                : asked.given(underA, Count.of(BigDecimal.ONE))
                        .given(underB, Count.of(BigDecimal.TWO)))
                .emptiness();

        return assertInstanceOf(EmptyInput.TwoRefinementsAtOnePosition.class,
                why.orElseThrow(() -> new AssertionError("no row is both cases, and nothing said so")),
                "what contradicts is the pair of assignments and not anything the rules say");
    }

    private static TermPath pathOf(InputDomain read, String spelled) {
        return read.positions().stream().map(Position::path)
                .filter(each -> each.toString().equals(spelled))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "no position at " + spelled + " among " + read.positions().stream()
                                .map(Position::path).toList()));
    }

    private static RuleReadingSource rulesOf(String source) {
        Compilation compilation =
                Compilation.ofSources(List.of(source), souther.compiler.meta.ModulePath.EMPTY);
        return RuleReadings.of(compilation, compilation.modules().get(0));
    }

    private static InputDomain reading(String source, String behavior) {
        Compilation compilation =
                Compilation.ofSources(List.of(source), souther.compiler.meta.ModulePath.EMPTY);
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES);
        return InputDomain.of(sigs.get(behavior), reading,
                TypeCardinality.Counts.workedOutIn(reading),
                souther.compiler.carrier.Membership.none());
    }
}
