package souther.compiler.values;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Constructor;
import java.lang.reflect.RecordComponent;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A reading is a value: nothing it holds can be changed after it is made.
 *
 * <p>What a query graph stops work on is whether an answer equals the one before it, so an answer
 * whose parts a caller can reach into is not an answer. A reading handed out with the map its maker
 * happened to be holding is one whose {@code equals} moves after it was compared, and — where it
 * admits nothing — one whose {@link AdmissibleValues#at} moves too.
 *
 * <p><b>Asked of every part, counted from the record itself.</b> The constructor copies the parts by
 * name, so a part added later is one it does not copy and nobody notices: the reading is still a
 * record, still equal to itself, and wrong only for a caller that kept the map it passed in. Written
 * out here as a list of parts to check, this test would be a copy of that constructor with the same
 * hole in it. Read off {@link Class#getRecordComponents}, a part added later is one it asks about.
 */
class EveryPartOfAReadingIsAValueTest {

    /** A part of a reading that something could be put into after the fact, and one for its maker
     *  to still be holding. */
    private record Handed(Object given, Object mutable) {}

    /**
     * Something to hand over for one part, and one for its maker to keep hold of.
     *
     * <p>Only the parts something can be put into afterwards have a second half. What the whole
     * thing is for is that the reading copied what it was handed, and there is nothing to copy
     * about a value.
     */
    private static Handed sampleFor(java.lang.reflect.Type declared) {
        Class<?> type = erased(declared);
        if (Map.class.isAssignableFrom(type)) {
            Map<Object, Object> out = new LinkedHashMap<>();
            out.put(sample(held(declared, 0)), sample(held(declared, 1)));
            return new Handed(out, out);
        }
        if (Collection.class.isAssignableFrom(type)) {
            Collection<Object> out = Set.class.isAssignableFrom(type)
                    ? new LinkedHashSet<>() : new ArrayList<>();
            out.add(sample(held(declared, 0)));
            return new Handed(out, out);
        }
        return new Handed(sample(declared), null);
    }

    /**
     * A value of whatever {@code declared} is, read as the shape it is declared to be.
     *
     * <p>Recursive over the declared type and not a table of the shapes met so far. A part of a
     * reading is a map of something to something, and what those are is part of what the part is —
     * answered by a rule per outer shape, {@code Map<?, List<Reason>>} is handed the value a
     * {@code Map<?, ValueSet>} wants and the constructor throws on the way in, so the part goes
     * unasked while the failure reads as this test's own. That happened once for the erased type
     * and would happen again one argument deeper.
     *
     * <p>A type variable is a position a reading is generic over, and a string stands for one:
     * nothing here reads what a position is, only that two of them are told apart.
     */
    private static Object sample(java.lang.reflect.Type declared) {
        Class<?> type = erased(declared);
        if (Map.class.isAssignableFrom(type)) {
            return Map.of(sample(held(declared, 0)), sample(held(declared, 1)));
        }
        if (Set.class.isAssignableFrom(type)) {
            return Set.of(sample(held(declared, 0)));
        }
        if (List.class.isAssignableFrom(type)) {
            return List.of(sample(held(declared, 0)));
        }
        if (type == boolean.class) {
            return false;
        }
        if (type == ValueSet.class) {
            return ValueSet.just(Value.text("5"));
        }
        if (type == UnreadReason.class) {
            return UnreadReason.FORM_NOT_READ;
        }
        if (type == AdmissibleValues.Held.class) {
            return new AdmissibleValues.Held.Alternatives<>(
                    Set.of(new AdmissibleValues.Box<>(Map.of())));
        }
        // A position, which this reading is generic over. What one is is the caller's; that two of
        // them are not the same one is all this needs.
        if (declared instanceof java.lang.reflect.TypeVariable<?> || type == Object.class) {
            return "a";
        }
        throw new IllegalArgumentException("nothing here knows how to hand over a " + declared
                + ": a part of a reading was added in a shape this has no sample of");
    }

    /** What {@code declared} holds at argument {@code which}, or {@code Object} where it says. */
    private static java.lang.reflect.Type held(java.lang.reflect.Type declared, int which) {
        return declared instanceof java.lang.reflect.ParameterizedType parameterized
                ? parameterized.getActualTypeArguments()[which] : Object.class;
    }

    /** The class a declared type is written in terms of. */
    private static Class<?> erased(java.lang.reflect.Type declared) {
        return declared instanceof java.lang.reflect.ParameterizedType parameterized
                ? (Class<?>) parameterized.getRawType()
                : declared instanceof Class<?> type ? type : Object.class;
    }

    /** Every part of one, and what was handed over for each, in the order the record declares. */
    private static List<Handed> handedOver(RecordComponent[] parts) {
        List<Handed> out = new ArrayList<>();
        for (RecordComponent part : parts) {
            out.add(sampleFor(part.getGenericType()));
        }
        return out;
    }

    @SuppressWarnings("unchecked")
    private static Object made(Class<?> of, List<Handed> handed) throws Exception {
        Constructor<?>[] every = of.getDeclaredConstructors();
        Constructor<?> canonical = every[0];
        for (Constructor<?> each : every) {
            if (each.getParameterCount() == handed.size()) {
                canonical = each;
            }
        }
        Object[] args = handed.stream().map(Handed::given).toArray();
        canonical.setAccessible(true);
        return canonical.newInstance(args);
    }

    /**
     * Nothing a reading holds may be added to once it has been made.
     *
     * <p>Both halves, because one of them alone is passed by a copy that was wrapped and by a wrap
     * that was not copied: what comes out refuses to be written to, and what the maker kept is no
     * longer the same thing.
     */
    @Test
    void nothingAReadingHoldsMayBeChangedAfterItIsMade() throws Exception {
        RecordComponent[] parts = AdmissibleValues.class.getRecordComponents();
        assertTrue(parts.length > 0);

        for (int i = 0; i < parts.length; i++) {
            RecordComponent part = parts[i];
            if (!Collection.class.isAssignableFrom(part.getType())
                    && !Map.class.isAssignableFrom(part.getType())) {
                continue;
            }
            List<Handed> handed = handedOver(parts);
            Object reading = made(AdmissibleValues.class, handed);
            Object held = part.getAccessor().invoke(reading);

            assertThrows(UnsupportedOperationException.class, () -> add(held),
                    part.getName() + " may be written to after the reading was made");

            Object stillTheirs = handed.get(i).mutable();
            add(stillTheirs);
            assertNotEquals(stillTheirs, part.getAccessor().invoke(reading),
                    part.getName() + " is the map its maker was holding, and moves when they write");
        }
    }

    /** And the same of what an alternative holds, which is a value for the same reason. */
    @Test
    void andNorMayAnAlternative() {
        Map<String, ValueSet> mine = new LinkedHashMap<>();
        mine.put("a", ValueSet.just(Value.text("5")));
        AdmissibleValues.Box<String> box = new AdmissibleValues.Box<>(mine);

        assertThrows(UnsupportedOperationException.class, () -> box.at().put("b", ValueSet.ANY));
        mine.put("b", ValueSet.just(Value.text("6")));
        assertEquals(Set.of("a"), box.at().keySet(), "what was said is what was said then");

        Set<AdmissibleValues.Box<String>> boxes = new LinkedHashSet<>();
        boxes.add(box);
        AdmissibleValues.Held.Alternatives<String> held =
                new AdmissibleValues.Held.Alternatives<>(boxes);

        boxes.add(new AdmissibleValues.Box<>(Map.of("b", ValueSet.ANY)));
        assertEquals(1, held.boxes().size(), "the alternatives are the ones it was made of");
    }

    @SuppressWarnings("unchecked")
    private static void add(Object collection) {
        if (collection instanceof Map<?, ?> map) {
            ((Map<Object, Object>) map).put("z", ValueSet.ANY);
            return;
        }
        ((Set<Object>) collection).add("z");
    }
}
