package souther.compiler.partition;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * The inputs the rows of a module ran with, by the type of the position each stood at: the values
 * a position of that type is known to take.
 *
 * <p>Which of these a search for one behavior's row looks at is decided by the type of the position
 * it grows a list at. Which it looks at first is decided by what the subject calls: the rows of
 * the behaviors it calls come before the rows of the module, so a behavior the subject has nothing
 * to do with, however many rows it has and whatever it is called, stands behind every value of one
 * it does.
 *
 * <p>Within each of the two, in the order the rows are met going across the behaviors one row of
 * each in turn: the first row of every behavior before the second row of any, and the behaviors in
 * the order they are called or declared. A search that stops after some of them has stopped at the
 * same place whatever the behaviors are called. A value met twice is there once, at the place it was
 * first met.
 *
 * <p>A value because the plan it stands in is held by an answer a store keeps: two of these are
 * equal where they hold the same values in the same order, and the hash is read off once.
 */
public final class InputsRowsRanWith {

    /** Nothing: a module whose rows ran with nothing, or a search that is handed none. */
    public static final InputsRowsRanWith NONE = new InputsRowsRanWith(Map.of());

    /** One row's input at one position: the value, and the type of the position. */
    public record Taken(Type type, ObservedValue value) {

        public Taken {
            Objects.requireNonNull(type, "a position has a type");
            Objects.requireNonNull(value, "a row's input is some value");
        }
    }

    /**
     * {@code value}, at a position of {@code type}, and every value it holds at a position of its
     * own, at any depth: an element of a list, a field of a record, the case of a sum, what an
     * optional holds, a key and a value of a map. Each stands at a position of its own type as
     * surely as the whole stands at its own, and a list grown by a value another row held at such a
     * position is a list the rows already speak of.
     *
     * <p>Read the way the values a run holds are read back, through the type the position has: a
     * name the type wears around another is taken off to see what the value holds, and the value is
     * kept as it was met. A value nothing was read of holds nothing to take.
     */
    public static void takenAt(Type type, ObservedValue value, RuleReadingSource source,
                               List<Taken> out) {
        out.add(new Taken(type, value));
        if (value.unread() != null) {
            return;
        }
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        ObservedValue inside = ObservedValue.wearing(view.wrappers(), value);
        if (inside == null || inside.unread() != null) {
            return;
        }
        switch (view.shape()) {
            case Shape.Sequence sequence -> {
                if (inside instanceof ObservedValue.Sequence held) {
                    for (ObservedValue element : held.elements()) {
                        takenAt(sequence.element(), element, source, out);
                    }
                }
            }
            case Shape.Product product -> {
                if (inside instanceof ObservedValue.Constructed made
                        && made.type().equals(product.name())) {
                    product.fields().forEach((name, fieldType) -> {
                        ObservedValue held = made.field(name);
                        if (held != null) {
                            takenAt(fieldType, held, source, out);
                        }
                    });
                }
            }
            case Shape.Sum sum -> {
                if (inside instanceof ObservedValue.Constructed made
                        && sum.reaches().cases().contains(made.type())) {
                    takenAt(Type.ref(made.type()), inside, source, out);
                }
            }
            case Shape.Optional optional -> {
                if (!(inside instanceof ObservedValue.Absent)) {
                    takenAt(optional.element(), inside, source, out);
                }
            }
            case Shape.Mapping mapping -> {
                if (inside instanceof ObservedValue.Mapping held) {
                    for (ObservedValue.Entry each : held.entries()) {
                        takenAt(mapping.key(), each.key(), source, out);
                        takenAt(mapping.value(), each.value(), source, out);
                    }
                }
            }
            case Shape.Scalar _, Shape.Unit _, Shape.Unresolved _, Shape.Cases _, Shape.Tuple _,
                 Shape.Function _, Shape.Uninhabited _, Shape.Bottom _, Shape.Erroneous _,
                 Shape.Undecided _ -> { }
        }
    }

    private final Map<Type, List<ObservedValue>> byType;

    private final int hash;

    private InputsRowsRanWith(Map<Type, List<ObservedValue>> byType) {
        this.byType = byType;
        this.hash = byType.hashCode();
    }

    /**
     * What the rows ran with: first what the rows of the behaviors the subject calls ran with, and
     * after them what the rows of the module ran with.
     *
     * <p>The rows of a behavior the subject calls are the rows whose inputs are what the subject
     * is handed to pass on, so they come first. The module's come after as what is known of the
     * type besides, and a behavior added to the module that the subject has nothing to do with
     * stands behind every value of one it does.
     *
     * @param called  the rows of each behavior the subject calls, in the order the calls are met
     * @param module  the rows of each behavior of the module, in the order they are declared; in
     *                both, a row is the inputs it was run with, one {@link Taken} for each
     *                position, in the order the rows are written
     */
    public static InputsRowsRanWith of(List<List<List<Taken>>> called,
                                       List<List<List<Taken>>> module) {
        Map<Type, Set<ObservedValue>> seen = new LinkedHashMap<>();
        take(called, seen);
        take(module, seen);
        if (seen.isEmpty()) {
            return NONE;
        }
        Map<Type, List<ObservedValue>> kept = new LinkedHashMap<>();
        seen.forEach((type, values) -> kept.put(type, List.copyOf(new ArrayList<>(values))));
        return new InputsRowsRanWith(Collections.unmodifiableMap(kept));
    }

    /** The values of {@code behaviors}, one row of each in turn, each behind those met before. */
    private static void take(List<List<List<Taken>>> behaviors,
                             Map<Type, Set<ObservedValue>> seen) {
        int most = behaviors.stream().mapToInt(List::size).max().orElse(0);
        for (int row = 0; row < most; row++) {
            for (List<List<Taken>> rows : behaviors) {
                if (row < rows.size()) {
                    for (Taken input : rows.get(row)) {
                        seen.computeIfAbsent(input.type(), _ -> new LinkedHashSet<>())
                                .add(input.value());
                    }
                }
            }
        }
    }

    /** The values a position of {@code type} was run with, in the order they were met. */
    public List<ObservedValue> of(Type type) {
        return byType.getOrDefault(type, List.of());
    }

    public boolean isEmpty() {
        return byType.isEmpty();
    }

    @Override
    public boolean equals(Object other) {
        return this == other || (other instanceof InputsRowsRanWith that
                && hash == that.hash && byType.equals(that.byType));
    }

    @Override
    public int hashCode() {
        return hash;
    }

    @Override
    public String toString() {
        return "InputsRowsRanWith" + byType;
    }
}
