package souther.compiler.partition;

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
 * <p>The module's, and no behavior's. Which of these a search for one behavior's row looks at is
 * decided by the type of the position it grows a list at, and not by who declared the value, so
 * adding or renaming a behavior that has nothing to do with the position changes nothing it looks
 * at.
 *
 * <p>In the order the rows are met going across the behaviors in the order they are declared, one
 * row of each in turn: the first row of every behavior before the second row of any. A behavior
 * with many rows does not stand before the rows of the ones declared after it, and a search that
 * stops after some of them has stopped at the same place whatever the behaviors are called. A value
 * met twice is there once, at the place it was first met.
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

    private final Map<Type, List<ObservedValue>> byType;

    private final int hash;

    private InputsRowsRanWith(Map<Type, List<ObservedValue>> byType) {
        this.byType = byType;
        this.hash = byType.hashCode();
    }

    /**
     * What the rows ran with.
     *
     * @param behaviors each behavior's rows, in the order the behaviors are declared; a row is the
     *                  inputs it was run with, one {@link Taken} for each position, in the order
     *                  the rows are written
     */
    public static InputsRowsRanWith of(List<List<List<Taken>>> behaviors) {
        Map<Type, Set<ObservedValue>> seen = new LinkedHashMap<>();
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
        if (seen.isEmpty()) {
            return NONE;
        }
        Map<Type, List<ObservedValue>> kept = new LinkedHashMap<>();
        seen.forEach((type, values) -> kept.put(type, List.copyOf(new ArrayList<>(values))));
        return new InputsRowsRanWith(Collections.unmodifiableMap(kept));
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
