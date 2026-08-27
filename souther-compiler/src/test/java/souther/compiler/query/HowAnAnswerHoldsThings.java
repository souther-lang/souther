package souther.compiler.query;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Supplier;

/**
 * Every way an answer comes to hold a collection, a map or an absence, one way per line.
 *
 * <p>What reads a thing for what it holds rests on comparing it comparing them, and nothing a class
 * says about itself tells one that keeps that from one that does not. So it is asked by building
 * two and comparing them, which takes a way of building one — and a way of building one is what a
 * list of class names is not.
 *
 * <p><b>Held against what a store actually holds.</b> A list somebody writes covers what they
 * thought of, and a check over it reads as though it covered what the compiler does. So
 * {@code EverythingAnAnswerHoldsMeansSomethingTest} asks whether every container a walk of the
 * corpora met is one of these, and a way of holding things that arrives without a line here fails
 * there rather than going unasked.
 */
final class HowAnAnswerHoldsThings {

    /** One way, built twice, so that what two of them come to can be asked. */
    static List<Supplier<Object>> all() {
        return List.of(
                () -> Map.of(new String("a"), new String("b")),
                () -> Map.of(new String("a"), new String("b"), new String("c"), new String("d")),
                () -> new LinkedHashMap<>(Map.of(new String("a"), new String("b"))),
                () -> new java.util.HashMap<>(Map.of(new String("a"), new String("b"))),
                () -> new java.util.TreeMap<>(Map.of(new String("a"), new String("b"))),
                () -> java.util.Collections.unmodifiableMap(
                        new LinkedHashMap<>(Map.of(new String("a"), new String("b")))),
                () -> java.util.Collections.unmodifiableSequencedMap(
                        new LinkedHashMap<>(Map.of(new String("a"), new String("b")))),
                () -> List.of(new String("a")),
                () -> List.of(new String("a"), new String("b"), new String("c")),
                () -> new java.util.ArrayList<>(List.of(new String("a"))),
                () -> java.util.Collections.unmodifiableList(
                        new java.util.ArrayList<>(List.of(new String("a")))),
                () -> Set.of(new String("a")),
                () -> Set.of(new String("a"), new String("b"), new String("c")),
                () -> new java.util.LinkedHashSet<>(Set.of(new String("a"))),
                () -> new java.util.HashSet<>(Set.of(new String("a"))),
                () -> java.util.Collections.unmodifiableSet(
                        new java.util.LinkedHashSet<>(Set.of(new String("a")))),
                () -> java.util.Collections.unmodifiableSequencedSet(
                        new java.util.LinkedHashSet<>(Set.of(new String("a")))),
                () -> Optional.of(new String("a")),
                // And the one the language ships that says it keeps none of the contract, so that
                // a line above going quiet is not the whole of what is asked.
                () -> {
                    Map<Object, Object> byWhichObject = new java.util.IdentityHashMap<>();
                    byWhichObject.put(new String("a"), new String("b"));
                    return byWhichObject;
                });
    }

    /** What the ways above are of, which is what a walk of a store is held against. */
    static Set<Class<?>> theClassesTheyComeBackAs() {
        Set<Class<?>> out = new java.util.LinkedHashSet<>();
        all().forEach(each -> out.add(each.get().getClass()));
        return out;
    }

    /**
     * Whether two of {@code type}, built apart and holding what compares equal, compare equal.
     *
     * <p>Which is the whole of the contract a walk leans on when it reads one for its members.
     */
    static boolean twoOfThemSayingTheSameThingAreEqual(Class<?> type) {
        for (Supplier<Object> each : all()) {
            if (each.get().getClass() == type) {
                return each.get().equals(each.get());
            }
        }
        throw new IllegalStateException("nothing here builds a " + type.getName()
                + ", so nothing here says whether it keeps the contract");
    }

    private HowAnAnswerHoldsThings() {
    }
}
