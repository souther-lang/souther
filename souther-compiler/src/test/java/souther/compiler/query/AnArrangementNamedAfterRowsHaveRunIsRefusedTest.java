package souther.compiler.query;

import souther.compiler.DoesNotComeBack;
import souther.compiler.observe.ArmObservation;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.RowOutcome;
import souther.compiler.source.SourceId;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A second arrangement is refused rather than quietly not taken.
 *
 * <p>{@link Db#running} takes what runs a compilation's programs once, and says why: it is beside
 * the memos rather than in them, so an answer worked out under one is not invalidated by another
 * being named, and the store goes on handing out the first one's answers. The arrangement a row is
 * run under is part of that thing. Named as an input it was invalidated like anything else the
 * outside sets; held by the implementation it is not, and a compilation that ran its rows and was
 * then given a second arrangement would answer for the second while having run under the first.
 *
 * <p>So the rule is the store's own, said one level in. What is checked here is that it is a
 * refusal: an arrangement that arrives too late is a caller getting the order wrong, and a
 * compilation that took it and went on answering from what it had would be telling that caller its
 * arrangement was in use.
 */
class AnArrangementNamedAfterRowsHaveRunIsRefusedTest {

    private static final String ONE_ROW = """
            module example.twice
            data N = Int
            data Out = Int
            behavior run : (n: N) -> Out constructs Out
            let run (n) = Out(n.value)
            example run
              | "answers": (N(1)) -> Out(1)
            """;

    /** Rows run, and then an arrangement said. */
    @Test
    void anArrangementSaidAfterTheRowsHaveRunIsRefused() {
        Compilation compilation = Compilation.ofSource(ONE_ROW, "Main");
        compilation.answerEverything();

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> compilation.withJvmExampleDeadlines(
                        DoesNotComeBack.overrunningOn(DoesNotComeBack.everythingAboutRowsOf("run"))));

        assertEquals(Disposition.HELD, onlyRowOf(compilation).disposition(),
                "and what it answered is what it ran, which is why the second one is refused: "
                        + refused.getMessage());
    }

    /** And before they have run, it is taken — which is the case every caller of it is. */
    @Test
    void anArrangementSaidBeforeAnyRowRunsIsTheOneTheRowsRunUnder() {
        Compilation compilation = Compilation.ofSource(ONE_ROW, "Main");
        compilation.withJvmExampleDeadlines(
                DoesNotComeBack.overrunningOn(DoesNotComeBack.everythingAboutRowsOf("run")));
        compilation.answerEverything();

        assertEquals(Disposition.INCOMPLETE, onlyRowOf(compilation).disposition());
    }

    private static RowOutcome onlyRowOf(Compilation compilation) {
        SourceId sourceId = compilation.exampleSourcesOf("example.twice").getFirst();
        List<RowOutcome> rows = compilation.db()
                .ask(new Output.Examples("example.twice", sourceId, ArmObservation.OMIT))
                .value().rows();
        assertEquals(1, rows.size(), rows.toString());
        return rows.get(0);
    }
}
