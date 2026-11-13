package souther.compiler.meaning;

import souther.compiler.collect.EachNodeOnce;

import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Objects;
import java.util.function.BiFunction;

/**
 * A reading that goes down the parts of statements, asked of each statement once.
 *
 * <p>A condition read through a name used twice is held by two statements, so the statements are a
 * graph, and the ways down a chain of names each using the one before it twice are two to its
 * length. A reader that recurses into the parts for itself pays for every way. Made here, a reading
 * answers each statement it meets once and hands that answer to every statement above it, so what
 * it costs is the statements and not the ways down to them.
 *
 * <p>The only way down the parts of a statement ({@link Proposition#anyPart},
 * {@link Proposition#everyPart}, {@link Proposition#eachPart}, {@link Proposition#sumOverParts},
 * {@link Proposition#overParts}, {@link Proposition#foldParts}) is handed an {@link EachOnce}, so a
 * reader that goes down them is one of these. It is made for one question and let go: what it
 * keeps is what that reading came to under the premises it was asked with, and a reading under
 * other premises is a reading of its own — or one {@linkplain InContext in a context}.
 *
 * <p>A reading that has an effect — one that gathers what it meets into a collection — has it once
 * for each statement, which is what gathering is: it adds what a statement says to a set, and a
 * statement met by two ways says it once. What a reading comes to is some answer: one that is none
 * is a value of its own ({@link java.util.Optional}), since a statement with no answer would be
 * worked out again for every way down to it.
 *
 * <p>Statements are told apart by identity ({@link EachNodeOnce}). Equal statements made apart are
 * two here; those made through {@link Proposition#all} and {@link Proposition#any} are the one kept
 * ({@link SharedPropositions}), which is where a graph of them comes from.
 *
 * <p>Not thread-safe: a reading is one thread's.
 *
 * @param <R> what the reading comes to for a statement
 */
public final class StatementReading<R> implements EachOnce<R> {

    /** What a reading comes to for one statement, and how it goes on into its parts. */
    @FunctionalInterface
    public interface At<R> {

        /**
         * What the reading comes to for {@code stated}. Its parts are read through {@code again},
         * which has the answer already for each one asked before.
         */
        R of(Proposition stated, StatementReading<R> again);
    }

    private final At<R> at;

    private final EachNodeOnce<Proposition, R> worked = new EachNodeOnce<>();

    private StatementReading(At<R> at) {
        this.at = at;
    }

    /** A reading that comes to what {@code at} says for each statement it is asked of. */
    public static <R> StatementReading<R> over(At<R> at) {
        return new StatementReading<>(at);
    }

    /** What the reading comes to for {@code stated}, worked out the first time it is asked. */
    @Override
    public R read(Proposition stated) {
        return worked.of(stated, each -> at.of(each, this));
    }

    /**
     * A reading whose answer for a statement turns on where it stands, which is {@code context}: a
     * statement is read once for each context it is met in, contexts told apart by
     * {@link Object#equals}.
     *
     * @param <C> what the answer turns on, an immutable value
     * @param <R> what the reading comes to
     */
    public static final class InContext<C, R> {

        /** What the reading comes to for one statement in one context. */
        @FunctionalInterface
        public interface AtIn<C, R> {

            /**
             * What the reading comes to for {@code stated} in {@code context}. Its parts are read
             * through {@code again}, in {@code context} through {@link #in}, or in another by
             * {@link #in} of that one.
             */
            R of(Proposition stated, C context, InContext<C, R> again);
        }

        private final AtIn<C, R> at;

        private final BiFunction<Proposition, C, C> relevantTo;

        private final Map<Proposition, Map<C, R>> worked = new IdentityHashMap<>();

        private InContext(AtIn<C, R> at, BiFunction<Proposition, C, C> relevantTo) {
            this.at = at;
            this.relevantTo = relevantTo;
        }

        /** A reading that comes to what {@code at} says for each statement and context. */
        public static <C, R> InContext<C, R> over(AtIn<C, R> at) {
            return new InContext<>(at, (_, context) -> context);
        }

        /**
         * The same, where what a statement comes to turns only on {@code relevantTo} of the
         * context it stands in: two contexts that differ in what the statement has nothing to do
         * with are one, so a statement is read once for what it can tell them apart by and not
         * once for each of the many contexts that are not it.
         */
        public static <C, R> InContext<C, R> over(AtIn<C, R> at,
                                                  BiFunction<Proposition, C, C> relevantTo) {
            return new InContext<>(at, relevantTo);
        }

        /** What the reading comes to for {@code stated} in {@code context}. */
        public R read(Proposition stated, C context) {
            C here = relevantTo.apply(stated, context);
            Map<C, R> known = worked.computeIfAbsent(stated, _ -> new HashMap<>());
            R found = known.get(here);
            if (found != null) {
                return found;
            }
            R made = Objects.requireNonNull(at.of(stated, here, this),
                    "what is read of a statement is some answer; one that is none is a value of"
                            + " its own (an Optional)");
            worked.get(stated).put(here, made);
            return made;
        }

        /** The reading in {@code context}, as the parts of a statement are handed it. */
        public EachOnce<R> in(C context) {
            return new In<>(this, context);
        }

        /** This reading, in one context. */
        public static final class In<C, R> implements EachOnce<R> {

            private final InContext<C, R> reading;

            private final C context;

            private In(InContext<C, R> reading, C context) {
                this.reading = reading;
                this.context = context;
            }

            @Override
            public R read(Proposition stated) {
                return reading.read(stated, context);
            }
        }
    }
}
