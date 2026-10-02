package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A record's rule relating two of its fields draws its line however many names that write nothing
 * are worn over the record.
 *
 * <p>A name wrapped round a value is not a step, so the record's fields stand where they stood and
 * the rule cuts the same number. What the line is drawn from is the rule as a reading read it, and
 * its reads are bound to the value of the declaration that reading is of. That binding, beside the
 * record's own, is what the reading of lines knows the positions by ({@link DeclaredThresholds}).
 *
 * <p>Two names and not one. The second name writes nothing over a first that writes nothing, so it
 * is read as the first: its reads are bound to the first name's value and not to its own. Placed by
 * the name the signature wrote, the line would be looked for under a binding the reading never
 * made, and would not be drawn — while every bound the rules leave came out the same.
 */
class ARuleUnderNamesThatWriteNothingDrawsItsLineTest {

    private static final String SOURCE = """
            module example.worn

            data Span = { lo: Int, hi: Int }
                invariant ordered = lo <= hi

            data Once = Span
            data Twice = Once

            data Taken

            behavior take : (r: %s) -> Taken
            let take (r) = Taken
            """;

    @Test
    void theRecordDrawsTheLine() {
        assertFalse(cutsTaking("Span").isEmpty(),
                "a rule relating two positions reaches the reading that draws lines");
    }

    @Test
    void oneNameOverTheRecordDrawsTheSameLine() {
        assertEquals(cutsTaking("Span"), cutsTaking("Once"),
                "a name that is no step leaves the rule cutting the same number");
    }

    @Test
    void twoNamesOverTheRecordDrawTheSameLine() {
        assertEquals(cutsTaking("Span"), cutsTaking("Twice"),
                "and a second such name leaves it there as well");
    }

    /** What the lines drawn for an input of {@code type} cut, with the rule each is filed against
     *  dropped. */
    private static List<String> cutsTaking(String type) {
        Compilation compilation = Compilation.ofSource(SOURCE.formatted(type), "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                        .flatMap(List::stream).map(each -> each.diagnostic().code()).toList(),
                "the model under test is a program that can be written");
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain inputs =
                compilation.db().ask(new Adequacy.Inputs(module)).value().get("take");
        return DeclaredThresholds.between("take", inputs.reading(rules)).stream()
                .map(each -> String.valueOf(each.cuts()))
                .collect(Collectors.toList());
    }
}
