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
     * The strings a pattern admits, which are neither finitely many nor finitely many short of
     * everything.
     *
     * <p>A third shape because a format is a third kind of answer. {@code T[0-9]{13}} names ten
     * thousand billion strings and leaves out every other string there is, so neither of the two
     * above holds it — written as either, a reading would have to answer that the rule admits
     * everything, which is the answer that loses the rule.
     *
     * <p><b>Never empty and never everything.</b> Those two have their shapes already, and a second
     * spelling of either would be a set that {@link #isEmpty} and {@link #isAny} answer about by
     * asking which shape it is. {@link #matching} is where that is settled, and it is the only way
     * to one of these.
     *
     * <p>What the language holds is the whole of what this says. Two patterns accepting the same
     * strings are one set here, because a {@link souther.compiler.regex.Language} is its strings —
     * so a reading run twice over one model comes to values that are equal.
     *
     * <p><b>Over strings, as every set here is over one carrier.</b> {@link Cofinite} already means
     * every value of the carrier but these, so a set does not describe values of two kinds and never
     * did; what stands at a position is of the position's type. So a finite set met or joined with
     * one of these holds strings, and a value of another kind in it is a set belonging to no
     * position rather than a case for this to answer.
     */
    record Matching(souther.compiler.regex.Language language) implements ValueSet {

        public Matching {
            if (language == null) {
                throw new IllegalArgumentException("a pattern admits the strings of some language");
            }
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

    /**
     * The strings {@code language} admits.
     *
     * <p>The one way to a {@link Matching}, and where a language that turns out to be one of the
     * two shapes already here becomes that shape. A pattern nothing satisfies is the empty set and
     * not a pattern with no strings; one that accepts everything is every value and not a pattern
     * that happens to leave nothing out. Held otherwise, {@link #isEmpty} would be a question about
     * which shape a set is written in, and the answer would turn on how a rule was spelled.
     */
    static ValueSet matching(souther.compiler.regex.Language language) {
        if (language.isEmpty()) {
            return NONE;
        }
        if (language.isEverything()) {
            return ANY;
        }
        return new Matching(language);
    }

    /**
     * Whether {@code value} is one of these.
     *
     * <p>Here, so that a reader wanting it does not answer it by asking which shape a set is. Every
     * shape has its own way of holding what it holds — one names them, one names what it leaves out,
     * one holds a language — and a caller reading that for itself is a second place the shapes are
     * enumerated, which the day a third arrived is exactly where it was not.
     */
    default boolean has(Value value) {
        return switch (this) {
            case Finite it -> it.values().contains(value);
            case Cofinite it -> !it.excluded().contains(value);
            // A language is a set of strings, so nothing that is not one is in it.
            case Matching it -> value instanceof Value.Text text && it.language().has(text.value());
        };
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
                // Which of finitely many the language holds, asked of each. Exact and cheap: what
                // comes out is a subset of what was already written down, so no language is built.
                case Matching there -> new Finite(kept(here.values(), there::has));
            };
            case Cofinite here -> switch (other) {
                case Finite _ -> other.meet(this);
                case Cofinite there -> new Cofinite(both(here.excluded(), there.excluded()));
                case Matching _ -> other.meet(this);
            };
            case Matching here -> switch (other) {
                case Finite there -> new Finite(kept(there.values(), here::has));
                // The language less what is excluded, which is a language: a value written out is a
                // string the machine can be told to refuse, and the rest is untouched.
                case Cofinite there ->
                        matching(here.language().without(textsIn(there.excluded())));
                case Matching there -> matching(here.language().and(there.language()));
            };
        };
    }

    /** The strings among {@code values}, which are the only ones a language has anything to say
     *  about. */
    private static Set<String> textsIn(Set<Value> values) {
        Set<String> out = new LinkedHashSet<>();
        values.forEach(each -> {
            if (each instanceof Value.Text text) {
                out.add(text.value());
            }
        });
        return out;
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
                case Matching _ -> other.join(this);
            };
            case Cofinite here -> switch (other) {
                case Finite _ -> other.join(this);
                case Cofinite there -> new Cofinite(kept(here.excluded(),
                        there.excluded()::contains));
                case Matching _ -> other.join(this);
            };
            case Matching here -> switch (other) {
                // The language and the values written beside it, which is a language: what a set of
                // words costs to add is the words.
                case Finite there -> matching(here.language().with(textsIn(there.values())));
                // Everything except what is excluded and the language does not hold. A value
                // excluded there is admitted here where the language holds it, so it is excluded
                // from the two of them together only where neither has it — which is asked of each
                // of finitely many and builds nothing.
                case Cofinite there -> new Cofinite(kept(there.excluded(),
                        each -> !here.has(each)));
                case Matching there -> matching(here.language().or(there.language()));
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
