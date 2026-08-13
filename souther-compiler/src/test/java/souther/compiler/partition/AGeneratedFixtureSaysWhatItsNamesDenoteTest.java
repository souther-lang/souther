package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Ast;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Every name in a fixture this generator builds says what it denotes.
 *
 * <p>ADR-0067 says a pass that synthesizes a node states what its name means rather than writing a
 * spelling for someone else to resolve. This is the pass that did not: a fixture's constructions
 * carried the spelling alone, so the reader of them had to ask what it meant in whatever module it
 * happened to be read in, and got the wrong declaration where the module had one of that name and
 * none where it did not (issue #696).
 *
 * <p>Held over the whole tree of every row of a model reaching another module's declarations three
 * ways at once — bare, through an alias, and applied. The reader's own tests would pass on a tree
 * with the answer missing, because a reader can always fall back to the spelling; this is the
 * proposition that there is nothing to fall back from, and it belongs to the side that writes.
 */
class AGeneratedFixtureSaysWhatItsNamesDenoteTest {

    private static final String LIB = """
            module lib exposing ( Amount, Kind, Domestic, Overseas, When )

            data Amount = Int
            data When = Date

            data Domestic
            data Overseas
            data Kind = Domestic | Overseas
            """;

    private static final String APP = """
            module app exposing ( Req, Ok, No, Verdict, f )

            import lib as up

            data Req = { amount: up.Amount, kind: up.Kind, at: up.When, note: String? }

            data Ok
            data No
            data Verdict = Ok | No

            behavior f : (r: Req) -> Verdict
                constructs Ok, No
            let f (r) = { guard r.amount.value < 500 else Ok
                No }
            """;

    /** Every expression of every row the model is offered, at every depth. */
    private static List<Ast.Expr> everyNodeOfEveryRow() {
        Compilation compilation = Compilation.ofSources(List.of(LIB, APP), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Adequacy.Filling filling =
                compilation.db().ask(new Adequacy.Generated("app")).value().get("f");

        List<Ast.Expr> nodes = new ArrayList<>();
        java.util.stream.Stream
                .concat(filling.boundaries().rows().stream(), filling.pairs().rows().stream())
                .forEach(row -> row.inputs().forEach(input -> collect(input.value(), nodes)));
        return nodes;
    }

    private static void collect(Ast.Expr e, List<Ast.Expr> into) {
        if (e == null) {
            return;
        }
        into.add(e);
        Ast.forEachChild(e, child -> collect(child, into));
    }

    /** The names, each with what it denotes — and nothing carrying a spelling and no answer. */
    @Test
    void everyNameInARowCarriesWhatItDenotes() {
        List<Ast.Expr> nodes = everyNodeOfEveryRow();
        assertFalse(nodes.isEmpty(), "the model under test produces rows");

        List<String> unanswered = new ArrayList<>();
        for (Ast.Expr node : nodes) {
            if (node instanceof Ast.Var name && name.denotes() == null) {
                unanswered.add(name.name());
            }
            if (node instanceof Ast.NewData nd && nd.typeName().denotes() == null) {
                unanswered.add(nd.typeName().written());
            }
        }

        assertEquals(List.of(), unanswered);
    }

    /**
     * And each of them answers what it reaches, which is the question every table in the compiler is
     * asked with. A name that denotes something and reaches nothing cannot be built at all, so this
     * is the pair being present rather than a second reading of the first.
     */
    @Test
    void everyNameInARowAnswersWhatItReaches() {
        List<String> reached = new ArrayList<>();
        for (Ast.Expr node : everyNodeOfEveryRow()) {
            if (node instanceof Ast.Var name) {
                reached.add(name.reaches());
            }
        }

        assertEquals(List.of("Date", "None", "up.Amount", "up.Domestic", "up.Overseas", "up.When"),
                reached.stream().distinct().sorted().toList(),
                "the module's declarations through its alias, the language's own vocabulary as"
                        + " itself, and nothing under a declaration's own spelling");
    }
}
