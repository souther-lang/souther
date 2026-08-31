package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A sum has a value wherever one of its cases does, so a case the rules refuse leaves the input its
 * other cases.
 *
 * <p>The cases of a sum are a choice. Read as a conjunction — every case's rules met into one space
 * — a model with one refused case comes back as a behavior that takes nothing, and every comparison
 * written about it is answered {@code NoFeasibleInput} while the rows a reader is owed are rows an
 * author can write.
 *
 * <p>The same of a sequence, whose element is a value the input has where the sequence holds one.
 * An element declaration the rules refuse leaves the empty sequence, which is a value this behavior
 * takes.
 */
class AViableCaseSurvivesADeadSiblingTest {

    private static final String DEAD_CASE = """
            module g

            data Shared = { lo: Int, hi: Int }
            data A = { ...Shared, x: Int }
                invariant impossible = x >= 1 && x <= 0
            data B = { ...Shared, y: Int }
            data Q = A | B

            data Holder = { q: Q }

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    /**
     * The same, with the case refused by its own rules together with the rule the record wrote.
     *
     * <p>Neither {@code lo >= 10} nor {@code hi <= 5} refuses {@code A} on its own, and the record's
     * {@code lo <= hi} refuses nothing until it is read at the numbers the names stand at. So this
     * is a case that is empty only once the relation is carried, and it is the model that says the
     * carry and the choice are one change: carried into a conjunction of the cases, this refuses the
     * whole input.
     */
    private static final String DEAD_ONCE_THE_RELATION_IS_CARRIED = """
            module g

            data Shared = { lo: Int, hi: Int }
            data A = { ...Shared, x: Int }
                invariant low = lo >= 10
                invariant high = hi <= 5
            data B = { ...Shared, y: Int }
            data Q = A | B

            data Holder = { q: Q }
                invariant ordered = q.lo <= q.hi

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    private static final String DEAD_ELEMENT = """
            module g

            data Item = { charge: Int }
                invariant impossible = charge >= 1 && charge <= 0
            data Holder = { items: List<Item> }

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    @Test
    void aCaseItsOwnRulesRefuseLeavesTheInputItsOtherCases() {
        assertEquals(Optional.empty(), emptinessOf(DEAD_CASE),
                "every B is a row this behavior takes, so the input is not proved empty");
    }

    @Test
    void andSoDoesACaseRefusedOnlyOnceTheRelationIsCarried() {
        assertEquals(Optional.empty(), emptinessOf(DEAD_ONCE_THE_RELATION_IS_CARRIED),
                "every B is a row this behavior takes, so the input is not proved empty");
    }

    @Test
    void anElementTheRulesRefuseLeavesTheEmptySequence() {
        assertEquals(Optional.empty(), emptinessOf(DEAD_ELEMENT),
                "an empty list is a value this behavior takes, so the input is not proved empty");
    }

    private static Optional<EmptyInput> emptinessOf(String source) {
        InputDomain read = reading(source, "read");
        return read.quantities(symbolsOf(source)).emptiness();
    }

    private static Symbols symbolsOf(String source) {
        Compilation compilation =
                Compilation.ofSources(List.of(source), souther.compiler.meta.ModulePath.EMPTY);
        compilation.answerEverything();
        return Scopes.derived(compilation.db(), compilation.modules().get(0)).value();
    }

    private static InputDomain reading(String source, String behavior) {
        Compilation compilation =
                Compilation.ofSources(List.of(source), souther.compiler.meta.ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals(behavior)).findFirst().orElseThrow();
        return InputDomain.of(spec, sigs.get(behavior), symbols, ReadAs.THE_COMPILATION_DOES);
    }
}
