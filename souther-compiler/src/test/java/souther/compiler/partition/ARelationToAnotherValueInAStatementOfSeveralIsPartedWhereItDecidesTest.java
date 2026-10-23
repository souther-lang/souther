package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.BlockReason;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A relation of the input to another value, read as one part of a statement of several, parts the
 * values that settle it by lines on the input, in the cases where the statement turns on it.
 *
 * <p>{@code i.n > (if o.open then w else 5)} states a line at five where the order is not open and
 * a relation to the greatest a walk has kept where it is. Every {@code n} at or below nought is
 * below what the walk keeps, so the relation is false there whatever the walk kept; the line that
 * parts those values is read where the order is open, and the place is not said to be one the
 * other value is not shown to reach.
 */
class ARelationToAnotherValueInAStatementOfSeveralIsPartedWhereItDecidesTest {

    private static final String DECLARATIONS = """
            module demo

            data Item = { n: Int }
                invariant n >= 0 && n <= 100
            data Order = { items: List<Item>, nums: List<Int>, q: Int, floor: Int, open: Bool }
                invariant q >= 0 && floor >= 0
            """;

    @Test
    void theLinePartingWhatSettlesItIsReadWhereTheRelationDecides() {
        ComparisonAssessment.Several several = severalOf("""
                List.fold((w, i) -> if i.n > (if o.open then w else 5) then i.n else w,
                          0, o.items) <= 10""");
        ComparisonAssessment.Several.Part part = relationPart(several);
        ComparisonAssessment.AgainstAnotherValue relation =
                assertInstanceOf(ComparisonAssessment.AgainstAnotherValue.class, part.line());
        assertFalse(relation.settling().isEmpty(), several::toString);
        assertTrue(part.cases().stream().anyMatch(each -> each.condition().key().contains("o.open")),
                () -> "it decides where the order is open: " + several);
        assertEquals(part.cases().size(), part.readings().size(), several::toString);
        assertTrue(several.whatEachPlaceIsLeftWith().stream().noneMatch(
                        each -> each.why() instanceof BlockReason.RelationNotShownToReachEveryValue),
                several::toString);
    }

    /**
     * The control: the value found is the greatest of numbers between nought and a hundred, which
     * this does not work out, so no value of {@code q} is shown to settle the relation, no line
     * is read in any case, and the place keeps its reason. The cases where it decides are kept all
     * the same: what settles a relation is asked again over the rows that arrive in each.
     */
    @Test
    void whereNothingIsShownToSettleItThePlaceKeepsItsReason() {
        ComparisonAssessment.Several several = severalOf("""
                Option.withDefault(0, List.find(x -> x > 3, List.map(i -> i.n, o.items)))
                    >= o.q""");
        ComparisonAssessment.Several.Part part = relationPart(several);
        assertTrue(assertInstanceOf(ComparisonAssessment.AgainstAnotherValue.class, part.line())
                .settling().isEmpty(), several::toString);
        assertFalse(part.cases().isEmpty(), several::toString);
        assertEquals(List.of(), part.readings(), several::toString);
        assertTrue(several.whatEachPlaceIsLeftWith().stream().anyMatch(
                        each -> each.why() instanceof BlockReason.RelationNotShownToReachEveryValue),
                several::toString);
    }

    /**
     * What a statement is narrowed to where rows arrive is what the report says of it: the line
     * parting the discounts at nought is owed no IN point, and no place is said to be one the
     * walk's value is not shown to reach.
     */
    @Test
    void theLineIsDrawnInTheFinalPartition() {
        String report = reportOf("""
                List.fold((w, i) -> if i.n > (if o.open then w else 5) then i.n else w,
                          0, o.items) <= 50""");
        assertTrue(report.contains("no IN point is owed at o.items[*].n = 0 (comparison@"),
                report);
        assertFalse(report.contains("relates the value here to another value not shown to reach"),
                report);
    }

    /**
     * What an application states about a value no position holds is parted the same way: that
     * some element of {@code nums} is {@code q} holds nowhere while the list is empty, and that
     * parts the lengths of the list.
     */
    @Test
    void anApplicationStatingARelationToAnotherValuePartsWhatSettlesIt() {
        ComparisonReadings.Reading contains = walked("List.contains(o.q, o.nums)").stream()
                .filter(each -> each.statement() instanceof ComparisonReadings.Stated.AnApplication)
                .findFirst().orElseThrow();
        ComparisonAssessment read = assertInstanceOf(BoundaryPolicy.Standing.Admitted.class,
                contains.standing()).read();
        ComparisonAssessment.AgainstAnotherValue relation =
                assertInstanceOf(ComparisonAssessment.AgainstAnotherValue.class, read,
                        read::toString);
        assertFalse(relation.settling().isEmpty(), read::toString);
    }

    /**
     * Nothing arrives at a relation behind a guard the declarations rule out, which is not a
     * relation no line was shown for: the place says what it says of a line nothing arrives at.
     */
    @Test
    void aRelationNothingArrivesAtIsNotOneNotShownToReachTheValues() {
        String report = reportOf("""
                if o.q < 0 then
                    List.fold((w, i) -> if i.n > (if o.open then w else 5) then i.n else w,
                              0, o.items) <= 50
                else true""");
        assertFalse(report.contains("relates the value here to another value not shown to reach"),
                report);
        assertTrue(report.contains("no row that arrives at it takes the way to the comparison"),
                report);
    }

    /** The adequacy report of a behavior that asks {@code condition} of an order. */
    private static String reportOf(String condition) {
        Compilation compilation = Compilation.ofSource(DECLARATIONS + """

                data Within
                data Needs

                behavior approval : (o: Order) -> Within | Needs

                let approval (o) =
                    if (%s) then Within else Needs
                """.formatted(condition.indent(8).strip()), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList());
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static ComparisonAssessment.Several.Part relationPart(
            ComparisonAssessment.Several several) {
        return several.parts().stream()
                .filter(each -> each.line() instanceof ComparisonAssessment.AgainstAnotherValue)
                .findFirst().orElseThrow(() -> new AssertionError(several.toString()));
    }

    /** The statement of several that {@code condition}'s comparisons include. */
    private static ComparisonAssessment.Several severalOf(String condition) {
        return walked(condition).stream()
                .map(each -> assertInstanceOf(BoundaryPolicy.Standing.Admitted.class,
                        each.standing()).read())
                .filter(ComparisonAssessment.Several.class::isInstance)
                .map(ComparisonAssessment.Several.class::cast)
                .filter(several -> several.parts().stream().anyMatch(
                        each -> each.line() instanceof ComparisonAssessment.AgainstAnotherValue))
                .findFirst().orElseThrow(() -> new AssertionError(condition));
    }

    private static List<ComparisonReadings.Reading> walked(String condition) {
        Compilation compilation = Compilation.ofSource(DECLARATIONS + """

                behavior f : (o: Order) -> Int
                let f (o) =
                    if (%s) then 1 else 0
                """.formatted(condition.indent(8).strip()), "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model compiles");
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        AnalysisBody analysis = checked.analysisBodies().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("f");
        InputReading read = inputs.reading(rules);
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        return ComparisonReadings.of("f", analysis, read, reads,
                CountWitnesses.AtComparisons.NONE).comparisons();
    }
}
