package souther.compiler.types;

import org.junit.jupiter.api.Test;

import java.lang.reflect.RecordComponent;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A type says in its own declaration whether it holds a type: a {@link Type.Compound} does and a
 * {@link Type.Leaf} does not. {@link Type#mapChildren} is the one place that says which positions a
 * compound holds, so a constructor added later is written there and every walk expressed over it
 * follows.
 *
 * <p>The samples are read back by reflection rather than by naming each position again here. A
 * position added to a constructor is rewritten or it is not, and asking the record what it holds is
 * how this notices without being told.
 */
class EveryPositionOfATypeIsRewrittenTest {

    /** What a rewrite put there. No sample holds it, so finding it means the position was written. */
    private static final Type REWRITTEN = Type.ref(new TypeName("m", "Rewritten"));

    private static final TypeName A = new TypeName("m", "A");
    private static final BindingOwner CALL = new BindingOwner.OfValue("m", "f");

    private static List<Type> compounds() {
        return List.of(
                Type.list(Type.INT),
                Type.set(Type.INT),
                Type.option(Type.INT),
                Type.map(Type.STRING, Type.INT),
                Type.tuple(List.of(Type.INT, Type.STRING)),
                Type.fn(List.of(Type.INT, Type.STRING), Type.BOOL));
    }

    private static List<Type> leaves() {
        return List.of(
                Type.INT,
                Type.ref(A),
                Type.var("'a"),
                new Type.MetaVar(CALL, "'a"),
                Type.NOTHING,
                Type.NEVER,
                Type.ERRONEOUS,
                Type.union(Set.of(A)));
    }

    @Test
    void everyCompoundConstructorHasASample() {
        assertEquals(constructorsOf(Type.Compound.class), classesOf(compounds()));
    }

    @Test
    void everyLeafConstructorHasASample() {
        assertEquals(constructorsOf(Type.Leaf.class), classesOf(leaves()));
    }

    /**
     * Each position is given a mark of its own, so what comes back says more than that something
     * was written: a position left alone holds no mark, one written twice holds a mark another
     * position was given, and a rebuild that puts an answer in the wrong slot holds them out of
     * order. The result is read back through the record rather than through the walk under test, so
     * a position the walk never knew about is still counted.
     */
    @Test
    void everyPositionThatHoldsATypeIsRewrittenOnceAndInTheOrderItIsWritten() {
        for (Type before : compounds()) {
            List<Type> marks = new ArrayList<>();
            Type after = Type.mapChildren(before, held -> {
                Type mark = Type.ref(new TypeName("m", "Mark" + marks.size()));
                marks.add(mark);
                return mark;
            });
            assertTrue(marks.size() > 0, before.getClass().getSimpleName() + " holds no type");
            assertEquals(marks, typesHeldBy(after),
                    after.getClass().getSimpleName() + " does not hold what it was answered");
        }
    }

    /** Every type {@code t} holds, read off the record in the order its positions are written. */
    private static List<Type> typesHeldBy(Type t) {
        List<Type> held = new ArrayList<>();
        for (RecordComponent slot : t.getClass().getRecordComponents()) {
            collect(read(slot, t), held);
        }
        return held;
    }

    private static void collect(Object value, List<Type> into) {
        switch (value) {
            case Type t -> into.add(t);
            case java.util.Collection<?> xs -> xs.forEach(x -> collect(x, into));
            case java.util.Map<?, ?> m -> m.values().forEach(x -> collect(x, into));
            case Object[] xs -> {
                for (Object x : xs) {
                    collect(x, into);
                }
            }
            case null, default -> { }
        }
    }

    private static Object read(RecordComponent slot, Type of) {
        try {
            return slot.getAccessor().invoke(of);
        } catch (ReflectiveOperationException e) {
            throw new AssertionError("cannot read " + slot, e);
        }
    }

    @Test
    void aLeafIsAnsweredAsItWasGiven() {
        for (Type leaf : leaves()) {
            assertSame(leaf, Type.mapChildren(leaf, t -> REWRITTEN));
        }
    }

    @Test
    void aRewriteThatChangesNothingAnswersTheTypeItWasGiven() {
        for (Type before : compounds()) {
            assertSame(before, Type.mapChildren(before, t -> t));
        }
    }

    @Test
    void aChildIsVisitedOnceAndInTheOrderItIsWritten() {
        assertEquals(List.of(Type.STRING, Type.INT), childrenOf(Type.map(Type.STRING, Type.INT)));
        assertEquals(List.of(Type.INT, Type.STRING, Type.BOOL),
                childrenOf(Type.fn(List.of(Type.INT, Type.STRING), Type.BOOL)));
        assertEquals(List.of(Type.INT), childrenOf(Type.list(Type.INT)));
    }

    @Test
    void aLeafHasNoChildren() {
        for (Type leaf : leaves()) {
            assertEquals(List.of(), childrenOf(leaf), leaf + " holds no type");
        }
    }

    private static List<Type> childrenOf(Type t) {
        List<Type> seen = new ArrayList<>();
        Type.forEachChild(t, seen::add);
        return seen;
    }

    /** Every constructor under {@code sealed}, descending through the interfaces between. */
    private static Set<Class<?>> constructorsOf(Class<?> sealed) {
        Class<?>[] permitted = sealed.getPermittedSubclasses();
        if (permitted == null) {
            return Set.of(sealed);
        }
        Set<Class<?>> out = new LinkedHashSet<>();
        for (Class<?> under : permitted) {
            out.addAll(constructorsOf(under));
        }
        return out;
    }

    private static Set<Class<?>> classesOf(List<Type> samples) {
        Set<Class<?>> out = new LinkedHashSet<>();
        for (Type sample : samples) {
            out.add(sample.getClass());
        }
        return out;
    }

}
