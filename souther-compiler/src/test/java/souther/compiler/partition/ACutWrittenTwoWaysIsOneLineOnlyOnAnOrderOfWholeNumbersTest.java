package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhereEachLineDecides;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * {@code x > 5} and {@code x >= 6} are one line where {@code x} is an {@code Int}, which no value
 * stands between five and six on, and two where it is a {@code Decimal}, where every value
 * between them is one {@code x} can be: whether a number of the input is whole is asked of the
 * order the input measures it on, from the declaration through to the carrier.
 */
class ACutWrittenTwoWaysIsOneLineOnlyOnAnOrderOfWholeNumbersTest {

    /** How many lines {@code g} draws, its input {@code x} declared {@code type}. */
    private static int lines(String type, String above, String atLeast) {
        String source = """
                module demo exposing (g)

                behavior g : (x: TYPE, h: Bool) -> Bool
                let g (x, h) = x > ABOVE && (x >= AT_LEAST || h)
                """.replace("TYPE", type).replace("AT_LEAST", atLeast).replace("ABOVE", above);
        Compilation compilation = Compilation.ofSource(source, "Main");
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        assertNotNull(checked, "the model compiles: " + compilation.errors());
        AnalysisBody analysis = checked.analysisBodies().get("g");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("g");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        Proposition stated = Pullback.ofATruth(Core.withoutStanding(analysis.core()), reads,
                inputs.reading(rules), Optional.empty()).proposition();
        return WhereEachLineDecides.in(stated, inputs.reading(rules).quantities()::countsWhole)
                .size();
    }

    @Test
    void oneLineOverWholeNumbersAndTwoOverDecimals() {
        assertEquals(1, lines("Int", "5", "6"));
        assertEquals(2, lines("Decimal", "5.0m", "6.0m"));
    }
}
