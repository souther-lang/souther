package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A term algebra with two kinds of root has to extend a path the same way at both of them, or one
 * value is two terms depending on which reader built it.
 *
 * <p>A place is a root and the fields read from it, and a computed value read a field off is a path
 * over that value. Both are chains, and reading one more field off either is a longer chain over the
 * same root — so the whole chain asked at once and the chain built a field at a time are one term.
 * Told apart, a reader that keys {@code x.a} from what {@code x} is and a reader that keys it from
 * the location would answer differently about one value, which is what having two authorities for
 * identity looks like from underneath.
 */
class ReadingAFieldDoesNotDecideWhichValueItIsReadFromTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final Hir.Binders BINDERS =
            new Hir.Binders(new BindingOwner.OfValue("demo", "test"));

    private final Term.Interner interned = new Term.Interner();

    @Test
    void aFieldReadOffAPlaceIsThatPlaceWithALongerPath() {
        BindingId x = BINDERS.binder("x", POS).id();

        assertEquals(interned.at(new Location(x, List.of("a"))),
                interned.on(interned.at(Location.of(x)), List.of("a")),
                "the whole chain and the field read off the root are one value");
    }

    @Test
    void aChainReachedAFieldAtATimeIsTheChainReachedAtOnce() {
        BindingId x = BINDERS.binder("x", POS).id();
        Term whole = interned.at(new Location(x, List.of("a", "b")));

        assertEquals(whole, interned.on(interned.at(Location.of(x)), List.of("a", "b")));
        assertEquals(whole,
                interned.on(interned.on(interned.at(Location.of(x)), List.of("a")), List.of("b")));
    }

    @Test
    void theSameHoldsOfAValueThatIsNowhere() {
        Term evaluated = interned.evaluated(new EvaluationId("an answer", POS));

        assertEquals(interned.on(evaluated, List.of("a", "b")),
                interned.on(interned.on(evaluated, List.of("a")), List.of("b")));
    }

    @Test
    void extendingAPathKeepsWhatItIsRootedAt() {
        BindingId x = BINDERS.binder("x", POS).id();
        BindingId y = BINDERS.binder("y", POS).id();
        Term evaluated = interned.evaluated(new EvaluationId("an answer", POS));

        assertNotEquals(interned.on(interned.at(Location.of(x)), List.of("a")),
                interned.on(interned.at(Location.of(y)), List.of("a")),
                "two bindings are two values, and reading a field off each does not join them");
        assertNotEquals(interned.on(interned.at(Location.of(x)), List.of("a")),
                interned.on(evaluated, List.of("a")),
                "a place and a value nothing names are not one value under the same field");
    }

    @Test
    void whichFieldsWereReadIsPartOfTheValue() {
        BindingId x = BINDERS.binder("x", POS).id();
        Term root = interned.at(Location.of(x));

        assertNotEquals(root, interned.on(root, List.of("a")));
        assertNotEquals(interned.on(root, List.of("a")), interned.on(root, List.of("b")));
        assertNotEquals(interned.on(root, List.of("a", "b")), interned.on(root, List.of("b", "a")));
    }
}
