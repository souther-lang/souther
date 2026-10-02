package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.DefaultStdlib;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.query.ReadAs;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Which subexpression standing at a node a table of subjects holds is one answer, however it is
 * asked. {@link Terms#heldAt} goes down a projection's names once against the table's chains; what
 * it answers is the first of {@link Core#subexpressionsAt} whose subject the table holds, each named
 * on its own — over every table of a projection's shorter projections, off a place and off a value
 * that is none.
 */
class ATableIsAskedOfAProjectionAsOfEachShorterOneTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static final List<String> NAMES = List.of("a", "b", "c", "d");

    private static BindingId binding(int index) {
        return new BindingId(new BindingOwner.OfValue("demo", "f"), index);
    }

    /** {@code base} with every name of {@link #NAMES} read off it, the nearest first. */
    private static Core.FieldProjection projected(Core base) {
        Core at = base;
        for (String name : NAMES) {
            at = Core.FieldProjection.then(at, name, Type.INT);
        }
        return (Core.FieldProjection) at;
    }

    /** What naming each subexpression in turn answers. */
    private static FactSubject eachInTurn(Terms terms, Core e, Denotations at, List<Term> held) {
        for (Core standing : Core.subexpressionsAt(e)) {
            FactSubject named = terms.subjectOf(standing, at);
            if (named != null && held.contains(named.identity())) {
                return named;
            }
        }
        return null;
    }

    private static void assertOneAnswerForEveryTable(Terms terms, Core base, Denotations at) {
        Core.FieldProjection p = projected(base);
        List<Core> standing = new ArrayList<>();
        Core.subexpressionsAt(p).forEach(standing::add);
        standing.add(base);
        List<Term> named = new ArrayList<>();
        for (Core each : standing) {
            named.add(terms.subjectOf(each, at).identity());
        }
        for (int table = 0; table < 1 << named.size(); table++) {
            List<Term> held = new ArrayList<>();
            for (int i = 0; i < named.size(); i++) {
                if ((table & 1 << i) != 0) {
                    held.add(named.get(i));
                }
            }
            Term.Chains chains = new Term.Chains(held);
            for (Core asked : standing) {
                assertEquals(eachInTurn(terms, asked, at, held), terms.heldAt(asked, at, chains),
                        "asked of " + asked + " against " + held);
            }
        }
    }

    @Test
    void offAPlace() {
        Terms terms = RuleReadings.termsOfNoClauseFiled(Symbols.none(DefaultStdlib.get()),
                ReadAs.THE_COMPILATION_DOES);
        BindingId n = binding(0);
        Denotations at = Denotations.none().location(n, AsPlaces.of(n), AsPlaces.term(n));
        assertOneAnswerForEveryTable(terms, new Core.Read("n", n, Type.INT, POS), at);
    }

    @Test
    void offAValueThatIsNoPlace() {
        Terms terms = RuleReadings.termsOfNoClauseFiled(Symbols.none(DefaultStdlib.get()),
                ReadAs.THE_COMPILATION_DOES);
        Core evaluated = new Core.Apply(new Core.Read("f", binding(1), Type.INT, POS), List.of(),
                Type.INT, POS);
        assertOneAnswerForEveryTable(terms, evaluated, Denotations.none());
    }
}
