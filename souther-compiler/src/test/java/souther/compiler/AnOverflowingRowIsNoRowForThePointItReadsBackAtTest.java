package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.FixtureTemplate;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row is offered for a point only where its run answers, and a candidate whose run aborts is
 * passed over for the next one composed.
 *
 * <p>The point at {@code c = 5} asks nothing of {@code d}, and {@code d - greatest - 2} runs below
 * the least {@code Int} for every {@code d} below one. So the candidate for {@code d} that comes
 * first aborts, and the row offered for the point is one with a {@code d} past it.
 */
class AnOverflowingRowIsNoRowForThePointItReadsBackAtTest {

    private static final String SOURCE = """
            module probe

            data Ok
            data No
            data Answer = Ok | No

            behavior f : (c: Int, d: Int) -> Answer
            let f (c, d) = if c >= 5 then (if d - 9223372036854775807 - 2 < 0 then Ok else No) else No
            """;

    @Test
    void aRowWhoseRunAbortsIsPassedOverForOneThatAnswers() {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        List<List<String>> rows =
                OfferedAtTheLines.of(compilation, compilation.modules().getFirst(), "f").rows()
                        .stream().map(row -> row.inputs().stream().map(FixtureTemplate::text)
                                .toList()).toList();

        assertFalse(rows.contains(List.of("5", "0")), "the row that aborts is not offered: " + rows);
        assertTrue(rows.contains(List.of("5", "1")), "the one that answers is: " + rows);
    }
}
