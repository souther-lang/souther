package souther.compiler.check;

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
     * And the pair the resolve pass is handed does carry one.
     *
     * <p>Here so that the check above is known to be able to see one. Told that the table carries
     * nothing by a test that could not have found anything, a reader learns nothing — and this is
     * the very thing the table was separated from.
     */
    @Test
    void thePairHandedToTheResolvePassCarriesOne() {
        assertEquals(List.of("elsewhere: Elsewhere"), asking(Resolve.Values.class));
    }

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
            return HELD.contains(named) || named.isRecord() || named.isEnum()
                    ? null : named.getSimpleName();
        }
        return type.getTypeName();   // a wildcard or a variable says nothing about what it stands for
    }
}
