package souther.compiler.reading;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.PieceDemand;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.Type;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A string a body parts and builds a newtype of the pieces of is read as one flow: this string, parted
 * at this code point, and that newtype.
 *
 * <p>A body that does this to two strings, with two separators and two types, states two flows and
 * not a separator and a type that either could be paired with.
 */
class TheStringsABodyPartsAndBuildsANewtypeOfAreReadAsFlowsTest {

    private static final String TWO_STRINGS = """
            module example.flows

            data Left = String
            data Right = String
            data Word = String
                invariant String.matches("[a-z]+", value)
            data Digits = String
                invariant String.matches("[0-9]+", value)
            data Both = { words: List<Word>, numbers: List<Digits> }

            behavior both : (left: Left, right: Right) -> Both
                constructs Both, Word, Digits

            let wordsOf (left: Left): List<Word> =
                List.flatMap(w -> if Word(w) as word then [ word ] else [],
                             List.drop(1, String.split("@", left.value)))

            let both (left, right) = Both
                { words = wordsOf(left)
                , numbers = List.flatMap(n -> if Digits(n) as digits then [ digits ] else [],
                                         String.split(";", right.value))
                }
            """;

    @Test
    void eachStringIsPairedWithItsOwnSeparatorAndItsOwnType() {
        List<PieceDemand> demands = read(TWO_STRINGS).piecesAttempted();

        assertEquals(List.of(
                "left parted at 64 into Word", "right parted at 59 into Digits"),
                demands.stream().map(each -> each.position() + " parted at " + each.separator()
                        + " into " + Type.show(each.attempted()).replaceAll("^.*\\.", "")).toList(),
                "two flows, each with the separator and the type of its own string");
        assertEquals(TermPath.of("left"), demands.getFirst().position());
    }

    private static CoverageRead.Read read(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, () -> "the model under test compiles: " + compilation.errors());
        String behavior = "both";
        Core body = checked.behaviorBodies().get(behavior);
        assertNotNull(body, "the behavior under test has a body");
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get(behavior);
        CoverageSites.Plan plan = checked.plan();
        assertNotNull(plan);
        return CoverageRead.of(behavior, checked.run(behavior), inputs.reading(rules));
    }
}
