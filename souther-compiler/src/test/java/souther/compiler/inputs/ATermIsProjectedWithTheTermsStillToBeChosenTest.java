package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.TypeCardinality;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Where a term runs is read with what the terms still to be chosen are on their own.
 *
 * <p>A relation between two terms bounds one by the ends the other has. Those ends are on the
 * rules only for a term somebody asked about, so a term asked alone is as wide as its own type
 * while the term beside it leaves it far less — and a search that chooses one and then the other
 * is handed the wide range for the first and spends what it is allowed at the end of it.
 *
 * <p>The years of dates are the terms, because the calendar is what gives a year its ends, and
 * the relation is taken in as a way's condition is.
 */
class ATermIsProjectedWithTheTermsStillToBeChosenTest {

    private static final String MODEL = """
            module g

            data Pair = { first: Date, second: Date }
            data Chain = { a: Date, b: Date, c: Date }
            data Stamp = { d: Date }
            data SideA = { ...Stamp, u: Int }
            data SideB = { ...Stamp, v: Int }
            data Side = SideA | SideB
            data Dated = { side: Side, m: Date }

            data Ok

            behavior dated : (x: Dated) -> Ok
            behavior pair : (p: Pair) -> Ok
            behavior chain : (c: Chain) -> Ok
            """;

    @Test
    void aRelationBoundsATermByTheEndsTheOtherHasFromItsType() {
        NumericTerm first = year("pair", "p.first");
        NumericTerm second = year("pair", "p.second");
        SearchRegion region = apart(region("pair"), second, first, 70);

        NumericDomain.Bounds alone = within(region.projectionOf(second));
        NumericDomain.Bounds beside = within(region.projectionOf(second, List.of(first)));
        NumericDomain.Bounds floorOfFirst = within(region.projectionOf(first));

        // Derived from the other's end and not written down, so the calendar is no part of it.
        assertEquals(floorOf(floorOfFirst) + 70, floorOf(beside));
        assertNotEquals(alone.min(), beside.min(), "alone it is as wide as its own type");
        assertEquals(alone.max(), beside.max(), "and nothing relates the top of it");
    }

    @Test
    void whatNoRelationReachesIsLeftAsWideAsItWas() {
        SearchRegion region = region("pair");
        NumericTerm first = year("pair", "p.first");
        NumericTerm second = year("pair", "p.second");

        assertEquals(region.projectionOf(first), region.projectionOf(first, List.of(second)));
    }

    @Test
    void theAnswerIsTheSameWhicheverOrderTheTermsStillToBeChosenAreInTheListOf() {
        NumericTerm a = year("chain", "c.a");
        NumericTerm b = year("chain", "c.b");
        NumericTerm c = year("chain", "c.c");
        SearchRegion region = apart(apart(region("chain"), a, b, 70), b, c, 5);

        NumericDomain.FormProjection one = region.projectionOf(a, List.of(b, c));

        assertEquals(one, region.projectionOf(a, List.of(c, b)));
        // Through both relations: the floor of the last is what the first stands on.
        assertEquals(floorOf(within(region.projectionOf(c))) + 75, floorOf(within(one)));
    }

    @Test
    void termsOfCasesNoRowHasTogetherLeaveTheTermAsWideAsItIsAlone() {
        NumericTerm m = year("dated", "x.m");
        NumericTerm underA = year("dated", "x.side@SideA.d");
        NumericTerm underB = year("dated", "x.side@SideB.d");
        SearchRegion region = apart(region("dated"), m, underA, 10);

        NumericDomain.FormProjection alone = region.projectionOf(m);

        assertNotEquals(alone, region.projectionOf(m, List.of(underA)));
        assertEquals(alone, region.projectionOf(m, List.of(underA, underB)));
        assertEquals(alone, region.projectionOf(m, List.of(underB, underA)));
    }

    @Test
    void aRegionThatHoldsNothingIsSaidToHoldNothingWhateverIsBesideIt() {
        NumericTerm first = year("pair", "p.first");
        NumericTerm second = year("pair", "p.second");
        SearchRegion contradicting = apart(region("pair"), second, first, 70)
                .assuming(LinearForm.difference(first, second), Rel.GE).taken();

        assertInstanceOf(NumericDomain.FormProjection.NothingIsLeft.class,
                contradicting.projectionOf(second, List.of(first)));
        assertInstanceOf(NumericDomain.FormProjection.NothingIsLeft.class,
                contradicting.projectionOf(second));
    }

    /** {@code later - earlier >= years}, taken in as a condition of a way is. */
    private static SearchRegion apart(SearchRegion region, NumericTerm later, NumericTerm earlier,
                                      long years) {
        LinearForm<NumericTerm> form = new LinearForm<>(ExactRatio.of(-years),
                Map.of(later, ExactRatio.ONE, earlier, ExactRatio.ONE.negated()));
        return region.assuming(form, Rel.GE).taken();
    }

    /** The lowest whole number the bottom of the run stands at. */
    private static long floorOf(NumericDomain.Bounds run) {
        return ((ExactAnswer.Held<BigInteger>) Count.number(run.min().at()).exactly().floor())
                .value().longValueExact();
    }

    private static NumericDomain.Bounds within(NumericDomain.FormProjection projection) {
        return assertInstanceOf(NumericDomain.FormProjection.Within.class, projection).bounds();
    }

    /** The year of the date at {@code spelled}, which runs as far as the calendar does. */
    private static NumericTerm year(String behavior, String spelled) {
        RuleReadingSource rules = rules();
        NumericTerm taken = NumericTerm.TakenOf.of(ValueName.Stdlib.operation("Date", "year"),
                ObservationSource.asItStands(pathOf(behavior, spelled)), TakenArguments.NONE,
                Type.Prim.DATE, ScopedDeclarations.wrapsOf(rules.symbols()), rules.symbols());
        assertNotNull(taken, "the year of a date is a number this compiler names");
        return taken;
    }

    private static TermPath pathOf(String behavior, String spelled) {
        InputDomain read = reading(behavior);
        return read.positions().stream().map(Position::path)
                .filter(each -> each.toString().equals(spelled))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "no position at " + spelled + " among " + read.positions().stream()
                                .map(Position::path).toList()));
    }

    private static SearchRegion region(String behavior) {
        return reading(behavior).quantities(rules()).region();
    }

    private static RuleReadingSource rules() {
        Compilation compilation =
                Compilation.ofSources(List.of(MODEL), souther.compiler.meta.ModulePath.EMPTY);
        compilation.answerEverything();
        return RuleReadings.of(compilation, compilation.modules().get(0));
    }

    private static InputDomain reading(String behavior) {
        Compilation compilation =
                Compilation.ofSources(List.of(MODEL), souther.compiler.meta.ModulePath.EMPTY);
        compilation.answerEverything();
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
