package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.frontend.CstFrontend;

import org.junit.jupiter.api.Test;

import java.lang.reflect.ParameterizedType;
import java.lang.reflect.RecordComponent;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a module can name is a table, and holding one reaches nothing.
 *
 * <p>The point of telling {@link Resolve.Reachable} from {@link Resolve.Values} apart. A reader that
 * wants to know what is in scope — an editor offering what may be written here — wants the first,
 * and the second carries a way of putting a further question to whatever supplied the modules.
 * Handed the pair, such a reader holds a way to reach the whole compilation, and what it kept is an
 * answer that is never equal to the next one, so nothing that read it is ever kept either.
 *
 * <p>Written as a property of the parts rather than as a list of them, because a list is a copy of
 * what the record already says and goes out of date by agreeing with itself. What is refused is a
 * part that can answer a question, whatever it is called — and inside a collection as well as
 * beside one, since a map of ways of asking is a way of asking.
 *
 * <p>It does not look inside another record. Both of the two that matter here are checked by name,
 * and a walk that followed every record would have to answer what to do about one that holds
 * itself.
 */
class TheTableAReaderHoldsReachesNothingTest {

    /** The kinds of thing a table is made of: what a name is spelled with, whether something holds
     *  of it, and the collections those are held in. */
    private static final Set<Class<?>> HELD =
            Set.of(String.class, boolean.class, int.class, Map.class, Set.class, List.class);

    @Test
    void everyPartOfTheTableIsAValue() {
        assertEquals(List.of(), asking(Resolve.Reachable.class),
                "a table is held by readers that must not be able to ask anything: a part that is"
                        + " neither a value nor a collection of values is a way of asking");
    }

    /**
     * And one put beside a table is found.
     *
     * <p>Here so that the check above is known to be able to see one. Told that the table carries
     * nothing by a test that could not have found anything, a reader learns nothing — and this is
     * the very thing the table was separated from. Written as a shape of its own rather than read
     * off the pair the resolve pass is handed, because that pair is no longer a record: what may be
     * put together is closed there, which is a different guarantee and is held elsewhere.
     */
    @Test
    void oneSetBesideATableIsFound() {
        assertEquals(List.of("elsewhere: Elsewhere"), asking(AsIfBesideOne.class));
    }

    /** A table with a way of asking beside it. */
    private record AsIfBesideOne(Resolve.Reachable table, Resolve.Elsewhere elsewhere) {}

    /**
     * And one held inside a collection is found.
     *
     * <p>The other half of knowing the check can see. A way of asking put beside the table is
     * refused by the arm above; one put in a map of them is what a table of names looks like from
     * the outside, and is what would go unseen by a check that read only the part's own type. There
     * is nothing in the compiler shaped like this, which is why it is written here.
     */
    @Test
    void oneHeldInsideACollectionIsFoundToo() {
        assertEquals(List.of("byName: Elsewhere"), asking(AsIfATableOfThem.class));
    }

    /** A table whose entries can each answer a question. */
    private record AsIfATableOfThem(Map<String, Resolve.Elsewhere> byName) {}

    /**
     * The pair says the same thing when its parts do.
     *
     * <p>It is not a record — what may be put together is closed — so what a record would have
     * written is written by hand, and this is what says the hand-written one still holds. An answer
     * a compilation remembers is compared with the next one to decide whether the work that read it
     * has to be done again, and one that never equals the last is an answer nothing is ever kept
     * past.
     */
    @Test
    void thePairIsAValue() {
        Ast.Module m = CstFrontend.parse("""
                module one exposing ( A )
                data A = { n: Int }
                """);

        assertEquals(Resolve.Values.of(m), Resolve.Values.of(m),
                "two of these over one module say the same thing");
        assertEquals(Resolve.Values.of(m).hashCode(), Resolve.Values.of(m).hashCode());
    }

    /** The parts of {@code held} that can answer a question. */
    private static List<String> asking(Class<?> held) {
        List<String> asking = new ArrayList<>();
        for (RecordComponent part : held.getRecordComponents()) {
            String reaching = reaching(part.getGenericType());
            if (reaching != null) {
                asking.add(part.getName() + ": " + reaching);
            }
        }
        return asking;
    }

    /**
     * Whether {@code named} is a value, which is what a table may hold.
     *
     * <p>A record and an enum are, and so is a sealed interface every arm of which is — a name
     * divided into the worlds it can come from is as much a value as one written as a single
     * record, and holding one reaches no more than holding an arm of it does. Read as "a record",
     * dividing a value into its cases would read as a way of asking, and what the reader would be
     * told to do about it is put it back.
     */
    private static boolean isValue(Class<?> named) {
        if (named.isRecord() || named.isEnum()) {
            return true;
        }
        if (!named.isSealed()) {
            return false;
        }
        for (Class<?> arm : named.getPermittedSubclasses()) {
            if (!isValue(arm)) {
                return false;
            }
        }
        return true;
    }

    /** What in {@code type} can answer a question, or null where none of it can. */
    private static String reaching(Type type) {
        if (type instanceof ParameterizedType parameterized) {
            String outer = reaching(parameterized.getRawType());
            if (outer != null) {
                return outer;
            }
            for (Type held : parameterized.getActualTypeArguments()) {
                String inner = reaching(held);
                if (inner != null) {
                    return inner;
                }
            }
            return null;
        }
        if (type instanceof Class<?> named) {
            return HELD.contains(named) || isValue(named) ? null : named.getSimpleName();
        }
        return type.getTypeName();   // a wildcard or a variable says nothing about what it stands for
    }
}
