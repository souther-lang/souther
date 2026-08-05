package souther.compiler.query;

import souther.compiler.check.ClauseDischarge;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeName;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the compiler says about each clause of an invariant: whether a construction of that type can
 * be judged safe from it, and by what kind of guard (spec §invariant-discharge-capability).
 *
 * <p>Once some clauses are statically dischargeable and others are not, the same {@code invariant}
 * keyword means two things to a reader, and nothing in the source distinguishes them. These pin the
 * answer, so the classification is the language's rather than whatever the checker manages today.
 */
class InvariantCapabilitiesTest {

    private static List<ClauseDischarge> of(String source, String type) {
        Compilation c = Compilation.ofDocuments(Map.of("a.sou", source), Set.of(), ModulePath.EMPTY);
        Map<TypeName, List<ClauseDischarge>> caps =
                c.db().ask(new Shapes.InvariantCapabilities("m.a")).value();
        return caps == null ? List.of() : caps.getOrDefault(new TypeName("m.a", type), List.of());
    }

    @Test
    void aRelationTheDomainReasonsOverIsDerivable() {
        List<ClauseDischarge> clauses = of("""
                module m.a
                data Money = Int
                    invariant value >= 0
                """, "Money");
        assertEquals(1, clauses.size());
        assertEquals(ClauseDischarge.Kind.DERIVABLE, clauses.get(0).kind());
    }

    @Test
    void aLengthIsDerivableToo() {
        List<ClauseDischarge> clauses = of("""
                module m.a
                data Lines = List<Int>
                    invariant List.length(value) >= 1
                """, "Lines");
        assertEquals(ClauseDischarge.Kind.DERIVABLE, clauses.get(0).kind());
    }

    @Test
    void aPredicateTakesAnExactMatch() {
        List<ClauseDischarge> clauses = of("""
                module m.a
                data Code = String
                    invariant String.matches("[A-Z]{2}", value)
                """, "Code");
        assertEquals(ClauseDischarge.Kind.EXACT_MATCH, clauses.get(0).kind());
    }

    @Test
    void aShapeTheCheckDoesNotReadIsRuntimeOnly() {
        List<ClauseDischarge> clauses = of("""
                module m.a
                data Kind = String
                    invariant match value with
                        | _ -> true
                """, "Kind");
        assertEquals(ClauseDischarge.Kind.RUNTIME_ONLY, clauses.get(0).kind());
        assertTrue(clauses.get(0).reason().isPresent(), "there is more than one way to be outside");
    }

    @Test
    void eachClauseOfAConjunctionIsAnsweredOnItsOwn() {
        // the two clauses of #222's target: a length the domain reasons over, and a uniqueness it can
        // only compare for identity
        List<ClauseDischarge> clauses = of("""
                module m.a
                data Row = { product: String }
                data Lines = List<Row>
                    invariant List.length(value) >= 1 && List.allDistinctBy(.product, value)
                """, "Lines");
        assertEquals(2, clauses.size(), "one answer per clause");
        assertEquals(ClauseDischarge.Kind.DERIVABLE, clauses.get(0).kind());
        assertEquals(ClauseDischarge.Kind.EXACT_MATCH, clauses.get(1).kind());
    }

    @Test
    void aClauseIsAnsweredAtItsOwnPosition() {
        List<ClauseDischarge> clauses = of("""
                module m.a
                data Row = { product: String }
                data Lines = List<Row>
                    invariant List.length(value) >= 1 && List.allDistinctBy(.product, value)
                """, "Lines");
        assertEquals(4, clauses.get(0).clause().line(), "both clauses are on the invariant's line");
        assertEquals(4, clauses.get(1).clause().line());
        assertTrue(clauses.get(0).clause().column() < clauses.get(1).clause().column(),
                "in the order they are written, so a position picks one out");
    }

    @Test
    void aClauseThroughAHelperIsAnsweredAsWhatTheHelperSays() {
        // the helper is expanded before the clause is read, so `twice(value) >= 0` is arithmetic
        List<ClauseDischarge> clauses = of("""
                module m.a
                let twice (n: Int): Int = n * 2
                data Even = Int
                    invariant twice(value) >= 0
                """, "Even");
        assertEquals(ClauseDischarge.Kind.DERIVABLE, clauses.get(0).kind());
        assertEquals(4, clauses.get(0).clause().line(), "reported where it is written, not where it expands");
    }
}
