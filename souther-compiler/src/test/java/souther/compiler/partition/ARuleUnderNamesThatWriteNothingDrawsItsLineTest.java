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
 * the rule cuts the same number. What the line is drawn from is the rule as the reading of the
 * outermost name read it: its reads are bound to that name's value, and that is the one binding,
 * beside the record's own, the reading of lines knows the positions by
 * ({@link DeclaredThresholds}). A reading of the outer name that took the reading of a name beneath
 * it as its own would carry reads bound to the inner name's value, which the reading of lines has
 * no position for, and the line would not be drawn — while every bound the rules leave came out the
 * same.
 *
 * <p>Two names and not one. The first name over the record reads the rule as one the walk reached
 * and the record reads it as its own clause, so those two readings are made apart whatever is
 * shared; it is from the second name up that one reading could be mistaken for the next.
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
