package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Ast;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.observe.Classification;
import souther.compiler.observe.Incompleteness;
import souther.compiler.partition.Axis;
import souther.compiler.partition.AxisId;
import souther.compiler.partition.Exclusions;
import souther.compiler.partition.GenerationReason;
import souther.compiler.partition.Generator;
import souther.compiler.partition.Partitions;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;
import souther.compiler.report.GeneratedRows;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the block says happened is what happened.
 *
 * <p>The note under a generated block was written from the presence of a reason: any reason at all
 * and it said the generation had stopped. A position left out is a reason and is not a stop — the
 * generator drops that position and fills the rest — so a block came out offering rows with a line
 * under them saying it had offered none. An author reading it is told both that there is work here
 * and that there is none.
 *
 * <p>Which of the two happened is the generator's to say and not the renderer's to infer, so it is
 * held in the value. These hold the two apart from the outside: one run that went on, one that
 * stopped, and the words that come out of each.
 */
class AGenerationThatWentOnDoesNotSayItStoppedTest {

    private static final String TRIP = """
            module example.trip

            data Domestic
            data Overseas
            data Kind = Domestic | Overseas

            data Request = { kind: Kind, urgent: Bool }

            data Accepted = { at: String }

            behavior submit : (request: Request) -> Accepted
                constructs Accepted

            let submit (request) = Accepted { at = "now" }
            """;

    private static Generator.Subject subject() {
        Compilation compilation = Compilation.ofSource(TRIP, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Ast.Module prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Symbols symbols = compilation.db().ask(new Shapes.Scope(module)).value();
        Ast.SpecBehavior spec = (Ast.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals("submit")).findFirst().orElseThrow();
        Sig sig = sigs.get("submit");
        return new Generator.Subject(spec.params().stream().map(Ast.Param::name).toList(),
                sig.inputTypes(), Partitions.of(spec, sig, symbols, Exclusions.NONE).axes(), symbols);
    }

    private static String written(Generator.GenerationResult result) {
        return GeneratedRows.of("example.trip",
                Map.of("submit", new Adequacy.Filling(result, Generator.GenerationResult.NONE)),
                false);
    }

    /**
     * One position could not be read and the others could, so the rest was filled.
     *
     * <p>The recorded reason is a truncation and what comes back is a withheld position, which is the
     * generator's own answer and not the classification's. What it decided is that no work is offered
     * there, and it decided that for either kind of unreadable value.
     */
    @Test
    void aPositionLeftOutIsNotAGenerationThatStopped() {
        Generator.Subject subject = subject();
        Axis first = subject.axes().get(0);
        Axis second = subject.axes().get(1);
        Map<AxisId, Classification> row = new LinkedHashMap<>();
        row.put(first.id(), new Classification.Unclassified(Incompleteness.atPosition(
                Incompleteness.Code.VALUE_TRUNCATED, first.id().behavior(), first.id().term())));
        row.put(second.id(), Classification.in(second.classes().get(0).id()));

        Generator.GenerationResult filled =
                Generator.fill(subject, List.of(row), Generator.CandidateCheck.ANY);

        assertFalse(filled.rows().isEmpty(), "the positions it could read were filled");
        assertInstanceOf(GenerationReason.PositionWithheld.class, filled.reasons().get(0));

        String written = written(filled);
        assertTrue(written.contains("example submit"), written);
        assertTrue(written.contains("no rows offered at `" + first.id() + "`"), written);
        assertFalse(written.contains("generation stopped"),
                "it offered rows two lines above: " + written);
    }

    /** And a run that did stop says so, in words a reader can act on. */
    @Test
    void aSearchThatRanOutSaysItStopped() {
        String written = written(new Generator.GenerationResult(List.of(), List.of(),
                List.of(new GenerationReason.SearchLimit("submit", 12))));

        assertEquals("// generation stopped for `submit`: 12 combinations past the row limit"
                + System.lineSeparator(), written);
    }

    /** One left is one combination. */
    @Test
    void theCountIsWrittenAsACount() {
        String written = written(new Generator.GenerationResult(List.of(), List.of(),
                List.of(new GenerationReason.SearchLimit("submit", 1))));

        assertTrue(written.contains("1 combination past"), written);
    }
}
