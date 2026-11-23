package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.observe.Figure;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.Optional;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The walk that tells what stops measuring a body reads none of the ways to its constructs, and
 * tells the figure the walk that reads them would tell ({@link WhatStopsMeasuring}): what a way
 * holds is where a line is asked, and not how many cases its statement has.
 *
 * <p>What an application is reached under is no way to its constructs and is read still: a line
 * drawn alike on several applications has a case for each condition they are reached under. Held at
 * each number of questions over lines under a fork and an arm of a match, the most cases being
 * those of a line on an inner closure's value past a condition on the outer closure's.
 */
class WhatStopsMeasuringIsShownWithoutReadingTheWaysTest {

    private static final String MODEL = """
            module demo

            data Kind = Open | Shut

            behavior g : (kind: Kind, limit: Int, a: Int, b: Int, c: Int) -> Bool
            let g (kind, limit, a, b, c) =
                if limit > 3 then
                    (match kind with
                        | Open -> List.any(
                            m -> List.any(n -> if m >= 5 then n <= 9 else n == 1, [ limit, c ]),
                            [ a, b ])
                        | Shut -> a > b)
                else a == limit
            """;

    @Test
    void theFigureIsTheOneTheWalkThatReadsTheWaysTells() {
        Compilation compilation = ACompiledModel.answered(MODEL);
        AnalysisBody analysis = compilation.db().ask(new Bodies.Checked("demo")).value()
                .analysisBodies().get("g");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("g");
        InputReading read = inputs.reading(rules);
        InputReads names = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        ComparisonReadings whole = OneReading.over(() -> ComparisonReadings.of("g", analysis,
                read, names, ComparisonWitnesses.AtComparisons.NONE));

        long stopped = IntStream.rangeClosed(0, 5).filter(questions ->
                Allowances.DECLARED.with(CompositionBudget.QUESTIONS_A_STATEMENT_IS_ASKED,
                        questions).over(() -> {
                            WhatStopsMeasuring stops = new WhatStopsMeasuring();
                            whole.comparisons().forEach(each -> stops.drawing(each.standing()));
                            Optional<Figure> told = OneReading.over(() ->
                                    ComparisonReadings.whatStopsMeasuring("g", analysis, read,
                                            names));
                            assertEquals(stops.figure(), told, "at " + questions);
                            return told.isPresent();
                        })).count();

        assertTrue(stopped > 1 && stopped < 6,
                "some numbers of questions stop the lines of several cases, and some do not: "
                        + stopped);
    }
}
