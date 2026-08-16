package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.lang.reflect.RecordComponent;
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
 * <p>Written as a property of the components rather than as a list of them, because a list is a
 * copy of what the record already says and goes out of date by agreeing with itself. What is being
 * refused is a component that can answer a question, whatever it is called.
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

    /** The parts of {@code held} that can answer a question. */
    private static List<String> asking(Class<?> held) {
        List<String> asking = new ArrayList<>();
        for (RecordComponent part : held.getRecordComponents()) {
            Class<?> type = part.getType();
            if (!HELD.contains(type) && !type.isRecord() && !type.isEnum()) {
                asking.add(part.getName() + ": " + type.getSimpleName());
            }
        }
        return asking;
    }
}
