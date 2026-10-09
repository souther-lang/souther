package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A relation a condition states is a line, drawn by the construct it was read off, wherever no
 * other construct written there draws it.
 *
 * <p>The partition reads lines off what conditions state. A comparison states itself, and the
 * relations an emptiness check or an application of an operation states were drawn by nobody where
 * no comparison was written for them: {@code List.all(l -> o.floor > 3, o.lines)} holds where
 * {@code o.lines} is empty or {@code o.floor} is above three, and the first of those is the
 * application's alone. Left to the fork around it, a statement read to the end was reported as a
 * rule about a value nothing worked out.
 *
 * <p>And a relation read to the end against a value no position holds — what an operation looked
 * up — is said as what it is: the value here related to another value, which divides none of the
 * values here.
 */
class WhatAConditionStatesIsDrawnWhereNothingElseDrawsItTest {

    private static final String DECLARATIONS = """
            module demo

            data Line = { price: Int }
            data Order = { lines: List<Line>, floor: Int, ceil: Int, key: String,
                           keys: List<String>, prices: Map<String, Int>, open: Bool }
            """;

    @Test
    void anApplicationDrawsWhatItAloneStates() {
        Walked walked = walked("List.all(l -> o.floor > 3, o.lines)");
        List<ComparisonReadings.Reading> applications = walked.comparisons().stream()
                .filter(each -> each.statement() instanceof ComparisonReadings.Stated.AnApplication)
                .toList();
        assertEquals(1, applications.size(), () -> "the application states lines: " + walked);
        assertEquals(Set.of("List.length(o.lines)", "o.floor"), positions(applications.getFirst()));
        assertEquals(List.of(), walked.leftToTheFork(), "nothing is left for the fork to state");
    }

    @Test
    void anEmptinessCheckDrawsTheRelationsNoComparisonWrites() {
        for (String check : List.of("List.length(List.take(o.floor, o.lines)) >= 1",
                "List.isEmpty(List.take(o.floor, o.lines))")) {
            Walked walked = walked(check);
            assertEquals(1, walked.comparisons().size(), () -> check + ": " + walked);
            assertEquals(Set.of("List.length(o.lines)", "o.floor"),
                    positions(walked.comparisons().getFirst()), check);
            assertEquals(List.of(), walked.leftToTheFork(), check);
        }
    }

    /**
     * A relation joined with whether a position is true is a line deciding where that truth says,
     * and a row says whether it is there: the check draws the line and the fork is left nothing.
     */
    @Test
    void aRelationBesideATruthIsALineDecidingWhereTheTruthHolds() {
        Walked walked = walked("List.length(if o.open then o.lines else []) >= 1");
        assertEquals(1, walked.comparisons().size(), () -> walked.toString());
        ComparisonReadings.Reading check = walked.comparisons().getFirst();
        assertEquals(Set.of("List.length(o.lines)"), positions(check));
        ComparisonAssessment.Several several = assertInstanceOf(ComparisonAssessment.Several.class,
                assertInstanceOf(BoundaryPolicy.Standing.Admitted.class, check.standing()).read());
        assertTrue(several.parts().getFirst().cases().stream()
                        .anyMatch(each -> each.key().contains("o.open")),
                () -> "it decides where the order is open: " + several);
        assertEquals(List.of(), walked.leftToTheFork());
    }

    /**
     * The control: the relations an emptiness check over a filter states are each read off the
     * comparison its closure writes, which draws them on each value, and the check draws none.
     */
    @Test
    void anEmptinessCheckWhoseRelationsAComparisonInsideItDrawsDrawsNone() {
        Walked walked = walked("List.isEmpty(List.filter(x -> x > 5, [o.floor, o.ceil]))");
        assertEquals(1, walked.comparisons().size(), () -> "the closure's comparison: " + walked);
        assertInstanceOf(ComparisonReadings.Stated.AComparison.class,
                walked.comparisons().getFirst().statement());
        assertEquals(Set.of("o.floor", "o.ceil"), positions(walked.comparisons().getFirst()));
    }

    @Test
    void aRelationToAValueNoPositionHoldsRelatesTwoValues() {
        Walked walked = walked("""
                match Map.get(o.key, o.prices) with
                    | Some p -> p > o.floor
                    | None -> false""");
        ComparisonReadings.Reading compared = walked.comparisons().getFirst();
        ComparisonAssessment read = assertInstanceOf(
                BoundaryPolicy.Standing.Admitted.class, compared.standing()).read();
        assertInstanceOf(ComparisonAssessment.AgainstAnotherValue.class, read, read::toString);
        assertEquals(List.of("o.floor"), read.whatEachPlaceIsLeftWith().stream()
                .map(each -> String.valueOf(each.at().path())).toList());
        assertTrue(read.whatEachPlaceIsLeftWith().stream().allMatch(each ->
                each.why() instanceof BlockReason.ComparisonRelatingTwoValues), read::toString);
    }

    /**
     * And an application stating that some element is another value relates the two, which is
     * what is said at each, and the fork around it is left nothing.
     */
    @Test
    void anApplicationRelatingTwoValuesSaysSoAtEach() {
        Walked walked = walked("List.contains(o.key, o.keys)");
        ComparisonReadings.Reading contains = walked.comparisons().getFirst();
        assertInstanceOf(ComparisonReadings.Stated.AnApplication.class, contains.statement());
        ComparisonAssessment read = assertInstanceOf(
                BoundaryPolicy.Standing.Admitted.class, contains.standing()).read();
        assertEquals(Set.of("o.keys[*]", "o.key"), read.whatEachPlaceIsLeftWith().stream()
                .map(each -> String.valueOf(each.at().path())).collect(Collectors.toSet()));
        assertTrue(read.whatEachPlaceIsLeftWith().stream().allMatch(each ->
                each.why() instanceof BlockReason.ComparisonRelatingTwoValues), read::toString);
        assertEquals(List.of(), walked.leftToTheFork());
    }

    /** The positions the lines of {@code each} divide. */
    private static Set<String> positions(ComparisonReadings.Reading each) {
        ComparisonAssessment read = assertInstanceOf(
                BoundaryPolicy.Standing.Admitted.class, each.standing()).read();
        List<ComparisonAssessment> lines = read instanceof ComparisonAssessment.Several several
                ? several.parts().stream().map(ComparisonAssessment.Several.Part::line).toList()
                : List.of(read);
        return lines.stream()
                .map(line -> String.valueOf(assertInstanceOf(
                        ComparisonAssessment.AtAPosition.class, line, read::toString).position()))
                .collect(Collectors.toSet());
    }

    /** What the walk of a body forking on {@code condition} read, and what its fork is left
     *  stating. */
    private record Walked(List<ComparisonReadings.Reading> comparisons,
                          List<ComparisonReadings.Atom> leftToTheFork) {}

    private static Walked walked(String condition) {
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
        ComparisonReadings walked = ComparisonReadings.of("f", analysis, read, reads, reads,
                WhatAnAnswerTakesUp.of(read));
        return new Walked(walked.comparisons(), walked.forks().stream()
                .flatMap(fork -> fork.leftHere().stream()).toList());
    }
}
