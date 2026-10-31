package souther.compiler.report;

import souther.compiler.observe.Incompleteness;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderObligationPointAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.Measurement;
import souther.compiler.query.ObligationSummary;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.query.Weakening;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row that never handed its values over is not a row with values that could not be read.
 *
 * <p>What it built before it stopped or was refused is a prefix of the inputs and not the inputs,
 * so a border asked where such a row stands has no position to read and nothing to say about the
 * value. A row that stopped says so once, where it stopped, and the border it may have been at is
 * held open by that; one that was refused is evidence of nothing and holds nothing open.
 */
class ARowThatHandedOverNoValuesIsNotReadAsOneThatCouldNotBeReadTest {

    private static final String SPIN =
            "partial let spin (n: Int) : Int = if n < 0 then 0 else spin(n + 1)\n";

    private static final String ROWS =
            "    | \"low\" : (1, Hit(0)) -> 1\n    | \"high\" : (10, Hit(3)) -> 3\n";

    private static String model(String rows) {
        return """
                module m

                data Hit = Int
                    invariant value >= 0

                behavior grade : (n: Int, h: Hit) -> Int

                let grade (n, h) = if n >= 10 then h.value else n

                """ + SPIN + """

                example grade
                """ + rows;
    }

    private static List<Weakening> causes(List<String> codes, String rows) {
        return WrittenWitness.refusedOnly(codes, model(rows)).assessment().uncertainties()
                .stream()
                .filter(AdequacyUncertainty.ByWeakening.class::isInstance)
                .map(each -> ((AdequacyUncertainty.ByWeakening) each).cause())
                .toList();
    }

    /** The points of the behavior's borders left undecided, which is what a stop holds open. */
    private static int undecidedPoints(List<String> codes, String rows) {
        AdequacyReport report = WrittenWitness.refusedOnly(codes, model(rows));
        AdequacyReport.BehaviorReport behavior =
                report.modules().getFirst().behaviors().getFirst();
        return ObligationSummary.of(behavior.account(), BorderObligationPointAssessment::owed)
                .undecided().size();
    }

    /** The declaration's own borders, which no fork drew, held open by the same stop. */
    private static Set<Weakening> declarationCauses(List<String> codes, String rows) {
        return WrittenWitness.refusedOnly(codes, model(rows)).modules().getFirst()
                .declarationsWeakenedBy().causes();
    }

    @Test
    void aRowStoppedBeforeItsValuesLeavesAPointOfAForkBorderUndecided() {
        int without = undecidedPoints(List.of(), ROWS);
        int with = undecidedPoints(List.of("E1910"), ROWS + "    | \"spin\" : (spin(1), Hit(0)) -> 1\n");

        assertTrue(with > without, "points undecided: " + without + " before the row, " + with
                + " after");
    }

    @Test
    void aRowStoppedBeforeItsValuesHoldsTheBordersOfADeclarationOpenToo() {
        // No row at the invariant's own line, so a row that stopped may be the one standing on it.
        String apart = "    | \"low\" : (1, Hit(3)) -> 1\n    | \"high\" : (10, Hit(3)) -> 3\n";
        Set<Weakening> without = declarationCauses(List.of(), apart);
        Set<Weakening> with = declarationCauses(List.of("E1910"),
                apart + "    | \"spin\" : (1, Hit(spin(1))) -> 1\n");

        assertFalse(without.stream().anyMatch(Weakening.ObservationIncomplete.class::isInstance),
                () -> "nothing stopped yet: " + without);
        assertTrue(with.stream().anyMatch(Weakening.ObservationIncomplete.class::isInstance),
                () -> "the stop, at a border no fork drew: " + with);
    }

    @Test
    void aRowRefusedBeforeItsValuesLeavesTheUndecidedPointsAsTheyWere() {
        assertEquals(undecidedPoints(List.of(), ROWS),
                undecidedPoints(List.of("E1903"), ROWS + "    | \"bad\" : (1, Hit(-1)) -> 1\n"));
        assertEquals(declarationCauses(List.of(), ROWS),
                declarationCauses(List.of("E1903"), ROWS + "    | \"bad\" : (1, Hit(-1)) -> 1\n"));
    }

    @Test
    void aRowStoppedBeforeItsValuesHoldsABorderOpenByItsStopAndNotByAValueItCouldNotRead() {
        List<Weakening> causes = causes(List.of("E1910"),
                ROWS + "    | \"spin\" : (spin(1), Hit(0)) -> 1\n");

        assertTrue(causes.stream().anyMatch(Weakening.ObservationIncomplete.class::isInstance),
                () -> "the stop, once: " + causes);
        assertFalse(causes.stream().anyMatch(Weakening.BorderValueUnreadable.class::isInstance),
                () -> "and no value it could not read: " + causes);
    }

    @Test
    void aRowStoppedAtItsSecondValueIsNotTakenAsHavingWrittenItsFirst() {
        List<Weakening> causes = causes(List.of("E1910"),
                "    | \"high\" : (10, Hit(3)) -> 3\n    | \"spin\" : (1, Hit(spin(1))) -> 1\n");

        assertFalse(causes.stream().anyMatch(Weakening.BorderValueUnreadable.class::isInstance),
                () -> "no value it could not read: " + causes);
        assertTrue(causes.stream().anyMatch(Weakening.ObservationIncomplete.class::isInstance),
                () -> "a point the stopped row may stand at is open: " + causes);
    }

    /**
     * The first input of a row that stopped at its second is placed where it was written, in the
     * generator as in the classes. {@code Red} is covered by it and {@code Blue} is not, so a row
     * for {@code Blue} is offered and the position is not withheld.
     */
    @Test
    void theGeneratorPlacesTheInputsAStoppedRowGotThroughTheSameWayTheClassesDo() {
        Compilation compilation = Compilation.ofSource("""
                module m

                data Red
                data Blue
                data Color = Red | Blue

                behavior f : (color: Color, n: Int) -> Int

                let f (color, n) =
                    match color with
                        | Red -> n
                        | Blue -> 0

                """ + SPIN + """

                example f
                    | "red" : (Red, 1) -> 1
                    | "red then stops" : (Red, spin(1)) -> 0
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        Adequacy.Filling generated = Adequacy.generatedOf(compilation.db(), "m").get("f");
        List<Adequacy.GenerationDisposition> uncovered = generated.generation().stream()
                .filter(each -> each.finding().kind() == Adequacy.Kind.AXIS_CLASS_UNCOVERED)
                .toList();
        assertFalse(uncovered.isEmpty(), "Blue is uncovered");
        for (Adequacy.GenerationDisposition each : uncovered) {
            assertInstanceOf(GenerationOutcome.Generated.class, each.outcome(),
                    () -> "a row for the class is offered, and the position is not withheld: "
                            + each.outcome());
        }
    }

    private static final String SHADES = """
            module m

            data Red
            data Blue
            data Color = Red | Blue
            data Light
            data Dark
            data Shade = Light | Dark

            behavior f : (color: Color, shade: Shade) -> Int

            let f (color, shade) =
                match color with
                    | Red -> match shade with | Light -> 1 | Dark -> 2
                    | Blue -> 0

            partial let spinShade (n: Int) : Shade = if n < 0 then Light else spinShade(n + 1)

            example f
                | "lit red" : (Red, Light) -> 1
            """;

    private static PartitionEvidence.AxisCoverage theShade(AdequacyReport report) {
        return report.modules().getFirst().behaviors().getFirst().partition().axes().stream()
                .filter(each -> each.path().endsWith("shade"))
                .findFirst().orElseThrow();
    }

    /**
     * A stop is one reason, and it is the row's own: the position the row never reached is unknown
     * because the row stopped, and not because a value could not be read.
     */
    @Test
    void anAxisThatAStoppedRowNeverReachedIsOpenByTheStopAndNotByAnUnreadableValue() {
        AdequacyReport report = WrittenWitness.refusedOnly(List.of("E1910"),
                SHADES + "    | \"stops\" : (Red, spinShade(1)) -> 2\n");
        PartitionEvidence.AxisCoverage shade = theShade(report);

        Measurement.Partial<?> partial = assertInstanceOf(Measurement.Partial.class,
                shade.reached(), () -> "Dark may be where the row would have been: "
                        + shade.reached());
        assertTrue(partial.weakening().causes().stream().anyMatch(each ->
                        each instanceof Weakening.ObservationIncomplete it
                                && it.met().fact().code()
                                        == Incompleteness.Code.ROW_EVALUATION_LIMIT_REACHED),
                () -> "the stop: " + partial.weakening());
        assertFalse(partial.weakening().causes().stream().anyMatch(each ->
                        each instanceof Weakening.ObservationIncomplete it
                                && it.met().fact().code() == Incompleteness.Code.VALUE_UNREADABLE),
                () -> "and no value it never had: " + partial.weakening());
    }

    /** The inputs the stopped row built stand where they were written. */
    @Test
    void theInputsAStoppedRowBuiltStillCoverTheirClass() {
        AdequacyReport report = WrittenWitness.refusedOnly(List.of("E1910"),
                SHADES + "    | \"stops\" : (Red, spinShade(1)) -> 2\n");
        PartitionEvidence.AxisCoverage color = report.modules().getFirst().behaviors()
                .getFirst().partition().axes().stream()
                .filter(each -> each.path().endsWith("color")).findFirst().orElseThrow();

        assertInstanceOf(Measurement.Complete.class, color.reached(),
                () -> "Red is covered and Blue is not, which is known: " + color.reached());
    }

    /** A row refused before its values is evidence of nothing, and leaves the class as it was. */
    @Test
    void anAxisIsNotOpenByARowRefusedBeforeItsValues() {
        AdequacyReport report = WrittenWitness.refusedOnly(List.of("E1903"),
                SHADES + "    | \"one input\" : (Red) -> 2\n");

        assertInstanceOf(Measurement.Complete.class, theShade(report).reached(),
                () -> "nothing is left to decide by the refused row: "
                        + theShade(report).reached());
    }

    /**
     * A stop and a value that really was cut short are two reasons, and each is kept. The value is
     * one the observation budget cut; the row beside it stopped before it had any.
     */
    @Test
    void aStopAndAValueCutShortAreBothKept() {
        String model = """
                module example.budget

                data Amount = Int
                    invariant value >= 0 && value <= 1000

                data Yes
                data No
                data Flag = Yes | No

                data Item = { a: String, b: String, c: String }
                data Group = { items: List<Item> }

                data Draft = { groups: List<Group>, cost: Amount, flag: Flag }
                data Ok = { n: Int }

                behavior take : (request: Draft) -> Ok
                    constructs Ok

                let take (request) =
                    match request.flag with | Yes | No -> Ok { n = request.cost.value }

                partial let spin (n: Int) : Int = if n < 0 then 0 else spin(n + 1)

                let someItems (n: Int): List<Item> =
                    List.map({ (i) -> Item { a = "x", b = "x", c = "x" } }, List.rangeInclusive(1, n))

                let someGroups (n: Int): List<Group> =
                    List.map({ (i) -> Group { items = someItems(64) } }, List.rangeInclusive(1, n))

                example take
                    | "cut short" : (Draft { groups = someGroups(64), cost = Amount(0), flag = Yes }) -> Ok { n = 0 }
                    | "stops" : (Draft { groups = [], cost = Amount(spin(1)), flag = Yes }) -> Ok { n = 0 }
                """;
        AdequacyReport report = WrittenWitness.refusedOnly(List.of("E1910"), model);
        PartitionEvidence.AxisCoverage flag = report.modules().getFirst().behaviors().getFirst()
                .partition().axes().stream().filter(each -> each.path().endsWith("flag"))
                .findFirst().orElseThrow();

        Measurement.Partial<?> partial = assertInstanceOf(Measurement.Partial.class,
                flag.reached(), () -> "No is covered by neither: " + flag.reached());
        Set<Incompleteness.Code> codes = new java.util.HashSet<>();
        partial.weakening().causes().forEach(each -> {
            if (each instanceof Weakening.ObservationIncomplete it) {
                codes.add(it.met().fact().code());
            }
        });
        assertTrue(codes.contains(Incompleteness.Code.VALUE_TRUNCATED), codes::toString);
        assertTrue(codes.contains(Incompleteness.Code.ROW_EVALUATION_LIMIT_REACHED),
                codes::toString);
        assertFalse(codes.contains(Incompleteness.Code.VALUE_UNREADABLE), codes::toString);
    }

    @Test
    void aRowRefusedBeforeItsValuesHoldsNothingOpen() {
        List<Weakening> causes = causes(List.of("E1903"),
                ROWS + "    | \"bad\" : (1, Hit(-1)) -> 1\n");

        assertFalse(causes.stream().anyMatch(Weakening.BorderValueUnreadable.class::isInstance),
                () -> "no value it could not read: " + causes);
    }

    @Test
    void aRowRefusedForTheNumberOfItsInputsHoldsNothingOpen() {
        List<Weakening> causes = causes(List.of("E1903"),
                ROWS + "    | \"two\" : (1, Hit(0), 5) -> 1\n");

        assertFalse(causes.stream().anyMatch(Weakening.BorderValueUnreadable.class::isInstance),
                () -> "no value it could not read: " + causes);
    }
}
