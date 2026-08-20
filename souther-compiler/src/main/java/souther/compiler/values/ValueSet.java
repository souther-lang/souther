package souther.compiler.values;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Which values one position may hold, as far as the rules about it were read.
 *
 * <p>Two shapes and not one, because {@code /=} does not leave a finite answer. {@code == "A"}
 * admits one value and {@code /= "A"} admits every value but one, and a reading with only the first
 * shape would have to answer the second with "anything" — which is true and is the answer that
 * loses {@code /= true} beside {@code /= false}. Written as the pair, the two are closed under
 * everything the connectives do to them.
 *
 * <p>{@link Cofinite} is over a carrier whose values are not counted out here. Where they can be
 * counted out — a boolean, an enumeration — what is excluded is taken away from them where the rule
 * is read, and what is left is a {@link Finite}. So a set that admits nothing is {@code Finite} with
 * nothing in it, and that is the only shape emptiness has: every reading that could reach it went
 * through values it had in hand.
 *
 * <p>{@link #ANY} is what a position nothing was read about holds, which is every value there is. It
 * is not "unread": whether a reading could take in the rules about a position is a separate answer
 * and is held separately ({@link AdmissibleValues}), because a position the model says nothing about
 * and a position this could not read say the same thing here and mean opposite things to a reader.
 */
public sealed interface ValueSet {

    /** These values and no others. */
    record Finite(Set<Value> values) implements ValueSet {

        public Finite {
            values = held(values);
        }
    }

    /** Every value of the carrier except these. */
    record Cofinite(Set<Value> excluded) implements ValueSet {

        public Cofinite {
            excluded = held(excluded);
        }
    }

    /**
     * A set kept as it was given, and unable to be changed after.
     *
     * <p>The order is the order the model writes the values in, and it is kept because something
     * will be written out of one of these: a position admitting three cases of an enumeration is
     * three classes, and which order a reader lists them in is not a thing to leave to how a set
     * happened to store them. {@code Set.copyOf} is what this is not — its iteration order is
     * settled per run of the compiler, so the same model would list them one way today and another
     * way tomorrow.
     */
    private static Set<Value> held(Set<Value> values) {
        return Collections.unmodifiableSet(new LinkedHashSet<>(values));
    }

    /** Every value there is, which is what the rules leave where they say nothing. */
    ValueSet ANY = new Cofinite(Set.of());

    /** Nothing at all. */
    ValueSet NONE = new Finite(Set.of());

    /** Just this one value. */
    static ValueSet just(Value value) {
        return new Finite(Set.of(value));
    }

    /** Everything but this one value. */
    static ValueSet allBut(Value value) {
        return new Cofinite(Set.of(value));
    }

    /** These values and no others. */
    static ValueSet oneOf(Set<Value> values) {
        return new Finite(values);
    }

    /** Whether no value is admitted, which is what refuses a declaration. */
    default boolean isEmpty() {
        return this instanceof Finite it && it.values().isEmpty();
    }

    /** Whether every value is admitted, so that nothing has been said. */
    default boolean isAny() {
        return this instanceof Cofinite it && it.excluded().isEmpty();
    }

    /** The values both admit — what two rules stated together leave. */
    default ValueSet meet(ValueSet other) {
        return switch (this) {
            case Finite here -> switch (other) {
                case Finite there -> new Finite(kept(here.values(), there.values()::contains));
                case Cofinite there -> new Finite(kept(here.values(),
                        each -> !there.excluded().contains(each)));
            };
            case Cofinite here -> switch (other) {
                case Finite _ -> other.meet(this);
                case Cofinite there -> new Cofinite(both(here.excluded(), there.excluded()));
            };
        };
    }

    /** The values either admits — what a rule stated as one of two alternatives leaves. */
    default ValueSet join(ValueSet other) {
        return switch (this) {
            case Finite here -> switch (other) {
                case Finite there -> new Finite(both(here.values(), there.values()));
                // Everything the other admits, less what it excludes and this does not have: a value
                // it excludes is admitted here where this names it, so it is no longer excluded from
                // the two of them together.
                case Cofinite there -> new Cofinite(kept(there.excluded(),
                        each -> !here.values().contains(each)));
            };
            case Cofinite here -> switch (other) {
                case Finite _ -> other.join(this);
                case Cofinite there -> new Cofinite(kept(here.excluded(),
                        there.excluded()::contains));
            };
        };
    }

    private static Set<Value> kept(Set<Value> these, java.util.function.Predicate<Value> keep) {
        Set<Value> out = new LinkedHashSet<>();
        these.forEach(each -> {
            if (keep.test(each)) {
                out.add(each);
            }
        });
        return out;
    }

    private static Set<Value> both(Set<Value> these, Set<Value> those) {
        Set<Value> out = new LinkedHashSet<>(these);
        out.addAll(those);
        return out;
    }
}
