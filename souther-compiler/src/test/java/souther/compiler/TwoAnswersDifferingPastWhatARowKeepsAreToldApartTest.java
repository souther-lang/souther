package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.observe.AnswerChange;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.Limits;
import souther.compiler.observe.ReplacedRun;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.source.SourceId;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * Whether a replaced arm changed what a row answered is asked of the two answers whole, not of what
 * a row keeps of its answer.
 *
 * <p>The two arms answer texts that are the same for longer than {@link Limits#DEFAULT} keeps of a
 * text and differ after it. What the row keeps of either answer is cut short at the same place, so
 * a comparison of the kept answers could say nothing — and a replacement that plainly changes the
 * answer would be one no run was seen to change.
 */
class TwoAnswersDifferingPastWhatARowKeepsAreToldApartTest {

    private static final String SHARED = "x".repeat(Limits.DEFAULT.maxText() + 64);

    private static final String MODEL = """
            module example.note

            data Note = String

            data Short
            data Long
            data Kind = Short | Long

            data Item = { kind: Kind }

            behavior describe : (item: Item) -> Note
                constructs Note

            let describe (item) = match item.kind with
                | Short -> Note("%sa")
                | Long  -> Note("%sb")

            example describe
                | "short" : (Item { kind = Short }) -> <?>
            """.formatted(SHARED, SHARED);

    @Test
    void aReplacementChangingTheAnswerOnlyPastWhatIsKeptIsSeenToChangeIt() {
        RowOutcome row = rowNamed("short");

        assertFalse(Limits.UNBOUNDED.admits(assertInstanceOf(AnswerObservation.Answered.class,
                        row.answer()).value()),
                "what the row keeps of its answer is cut short, which is what this is about: "
                        + row.answer());
        assertEquals(1, row.replaced().size(), "the one arm it went through, as its sibling: "
                + row.replaced());
        ReplacedRun run = row.replaced().getFirst();
        assertEquals(AnswerChange.CHANGED, run.changed(),
                "the two answers differ at their last character");
    }

    private static RowOutcome rowNamed(String name) {
        Compilation compilation = Compilation.ofSources(List.of(MODEL), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        List<RowOutcome> rows = new ArrayList<>();
        for (String module : compilation.modules()) {
            for (SourceId id : compilation.exampleSourcesOf(module)) {
                Output.Examples.Of ran = compilation.db()
                        .ask(Output.Examples.asked(compilation.db(), module, id)).value();
                if (ran != null) {
                    rows.addAll(ran.rows());
                }
            }
        }
        return rows.stream().filter(row -> row.identity().shown().equals(name)).findFirst()
                .orElseThrow(() -> new AssertionError("no row `" + name + "` in " + rows));
    }
}
