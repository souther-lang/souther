package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.ast.Hir;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A chain of names is kept as the chain one shorter and the last name, so that a chain one longer
 * is made in one step; what it is equal to and the number it hashes to are its names all the same,
 * however it was made — written out at once, a name at a time, or by another reading altogether.
 */
class AChainOfNamesIsOneValueHoweverItWasMadeTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final BindingId X =
            new Hir.Binders(new BindingOwner.OfValue("demo", "test")).binder("x", POS).id();

    @Test
    void aChainWrittenAtOnceIsTheChainMadeANameAtATime() {
        FieldPath atOnce = FieldPath.of(List.of("a", "b", "c"));
        FieldPath aNameAtATime = FieldPath.NONE.then("a").then("b").then("c");
        FieldPath inTwo = FieldPath.of(List.of("a")).then(FieldPath.of(List.of("b", "c")));

        assertEquals(atOnce, aNameAtATime);
        assertEquals(atOnce, inTwo);
        assertEquals(atOnce.hashCode(), aNameAtATime.hashCode());
        assertEquals(atOnce.hashCode(), inTwo.hashCode());
        assertEquals(List.of("a", "b", "c"), inTwo.names());
    }

    @Test
    void andAnyNameOrLengthApartIsAnotherChain() {
        FieldPath chain = FieldPath.of(List.of("a", "b"));
        assertNotEquals(chain, FieldPath.of(List.of("a", "c")));
        assertNotEquals(chain, FieldPath.of(List.of("b", "b")));
        assertNotEquals(chain, FieldPath.of(List.of("a")));
        assertNotEquals(chain, FieldPath.of(List.of("a", "b", "c")));
    }

    @Test
    void aPlaceIsOnePlaceHoweverItsFieldsWereMade() {
        Location written = new Location(X, List.of("a", "b"));
        Location made = new Location(X, Location.of(X).fields().then("a").then("b"));
        assertEquals(written, made);
        assertEquals(written.hashCode(), made.hashCode());
        assertEquals(List.of("a", "b"), made.path());
    }

    @Test
    void aTermReadOnANameAtATimeIsTheTermReadOnAtOnce() {
        Term.Interner interned = new Term.Interner();
        Term place = interned.at(Location.of(X));
        assertSame(interned.on(place, List.of("a", "b")),
                interned.on(interned.on(place, List.of("a")), List.of("b")));

        Term evaluated = interned.evaluated(new EvaluationId("an answer", POS, 0));
        assertSame(interned.on(evaluated, List.of("a", "b")),
                interned.on(interned.on(evaluated, List.of("a")), List.of("b")));
    }

    @Test
    void andTwoReadingsMakingItApartMakeOneTerm() {
        Term.Interner one = new Term.Interner();
        Term.Interner other = new Term.Interner();
        Term here = one.on(one.at(Location.of(X)), List.of("a", "b"));
        Term there = other.on(other.on(other.at(Location.of(X)), List.of("a")), List.of("b"));
        assertEquals(here, there);
        assertEquals(here.hashCode(), there.hashCode());
    }
}
