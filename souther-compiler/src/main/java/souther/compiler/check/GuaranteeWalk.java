package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

/**
 * A reader taken over the positions under a value, told what each one guarantees.
 *
 * <p>Mechanism and not meaning. What a declaration says is {@link TypeGuarantees}' answer and this
 * asks for it a position at a time; what this owns is getting to the positions — how deep to go,
 * which names were to be left out, and stopping where a record holds another of its own kind. Two
 * readers may walk to different depths and still be reading one model, which is the whole point of
 * keeping the two apart: a scope changes which positions were visited, never what a declaration
 * states at one.
 *
 * <p>Nothing here decides what a stop costs. A reader is told where the walk stopped and answers
 * that for itself, because the same stop means different things to different readers: a measurement
 * that has to account for every rule owes a line for what it did not read, and a reading that only
 * wants the relations it can state is short of nothing.
 */
final class GuaranteeWalk {

    private final TypeGuarantees guarantees;

    GuaranteeWalk(TypeGuarantees guarantees) {
        this.guarantees = guarantees;
    }

    /**
     * How far into a value's fields a walk over a body can afford to read.
     *
     * <p>A type's own invariant is what its fields guarantee, and a field's type carries its own;
     * past a couple of levels what a clause could be read against is a value the body would have had
     * to name, and it names it by reading it.
     *
     * <p>A cost bound and not a rule of the model: a rule four records down refuses the outermost
     * construction exactly as one on its own fields does. What a construction has to satisfy has no
     * depth at all, and a reader answering for that asks for one that has none.
     */
    static final int FIELDS_SEEDED = 2;

    /**
     * How far a reader is asking this walk to go.
     *
     * @param extent          how far down to read
     * @param stopAt          names this reader is supposing hold values whatever is written under
     *                        them, so nothing under one of them is read
     * @param withoutClauses  names whose own clauses this reader asked to leave out, what is under
     *                        them still being read
     */
    record Scope(Extent extent, Predicate<TypeSymbol> stopAt, Predicate<TypeSymbol> withoutClauses) {

        /** Every rule down to {@code positions} positions, wherever it is written. */
        static Scope asFarAs(int positions) {
            return new Scope(new Extent.AsFarAs(positions), _ -> false, _ -> false);
        }

        /** Every rule the model writes under this value. */
        static Scope everyPosition() {
            return new Scope(new Extent.EveryPosition(), _ -> false, _ -> false);
        }
    }

    /**
     * How far down a reader reads.
     *
     * <p>Two answers and not one number. A reader that cannot afford the whole value states what it
     * can afford; a reader whose question has no depth in it says so. Held as a number for both,
     * the second has to invent one — and the numbers that get invented are a bound belonging to some
     * other question, or a sentinel standing for "not applicable" inside a type that cannot say it.
     * Either way the depth a reader could afford becomes part of what a declaration is taken to say.
     */
    sealed interface Extent {

        /** Whether a position {@code down} steps from the root is one this reader reads. */
        boolean reaches(int down);

        /**
         * As far as the model goes.
         *
         * <p>What a value guarantees has no depth in it: a rule four records down refuses the
         * outermost value exactly as one on the top does, and a reading that stopped short would
         * make what a declaration says depend on how deeply an author nested a field. Terminating
         * because a name met on the way down is not entered again, which is a fact about the type
         * graph and not a budget.
         */
        record EveryPosition() implements Extent {

            @Override
            public boolean reaches(int down) {
                return true;
            }
        }

        /**
         * As far as {@code positions} steps down, and no further.
         *
         * <p>A cost bound, and only ever that. A reader states one where reading further is work it
         * cannot afford — never where the question it is asking runs deeper than it wants to go.
         */
        record AsFarAs(int positions) implements Extent {

            @Override
            public boolean reaches(int down) {
                return down <= positions;
            }
        }
    }

    /** Told what was read, what another reading answers for, and where this walk stopped. */
    interface Reader {

        /** What the declaration at {@code path} guarantees of the value there. */
        void guaranteed(String path, TypeGuarantee guarantee);

        /** Where the walk went no further, and what stood there. */
        default void stopped(String path, Type type, Stop why) {}

        /**
         * That rules stand under {@code path} which no reading here takes in, and which a reading
         * opened elsewhere answers for — the cases of a sum, what a container holds.
         *
         * <p>Not a stop. The position was read and what it states was heard; this says only that
         * something below it belongs to somebody else. Reported as a stop, a sum whose cases share a
         * spread would have to be either read or handed on, and it is both.
         */
        default void handedOn(String path, Type type) {}

        /** That a declaration at {@code path} writes these clauses and this reading could not state
         * them, so what they were about is not among what was handed over. */
        default void lostAClause(String path, List<RuleRef.Invariant> lost) {}
    }

    /**
     * Why a walk went no further.
     *
     * <p>Every one of them is this walk's own doing. A position it did not enter because nothing
     * there belongs to it is not a stop at all — that is {@link Reader#handedOn}, and it is answered
     * by the reading rather than by the walk. Held here as a stop, a position that both states rules
     * and leaves something below to another reading could only be one of the two.
     */
    enum Stop {

        /** As far down as the reader asked to be taken. Not a limit on the model: a rule four
         * records down refuses the outermost construction exactly as one on its own fields does. */
        PAST_THE_DEPTH,

        /** A name the reader is supposing holds values, so what is under it says nothing here. */
        ASKED_TO_STOP,

        /** Met already on the way down, and read where it was met. A record holding one of its own
         * kind stops here and nothing is short of anything for it. */
        ALREADY_ENTERED
    }

    /**
     * Take {@code reader} over {@code root} and the positions beneath it.
     *
     * <p>{@code path} names where {@code root} itself stands, and every position is named relative
     * to it.
     */
    void from(Core root, String path, Denotations at, Scope scope, Reader reader) {
        walk(root, path, at, 0, scope, new HashSet<>(), reader);
    }

    private void walk(Core root, String path, Denotations at, int depth, Scope scope,
                      Set<TypeSymbol> entered, Reader reader) {
        // Asked one at a time, because a stop says two things and only one of them is the same for
        // all of these: whether the rules under it were read, and whether a construction could have
        // got out of making the value they are about.
        if (!scope.extent().reaches(depth)) {
            reader.stopped(path, root.type(), Stop.PAST_THE_DEPTH);
            return;
        }
        // The reading first, because what stands here is what this walk's own limits are about: the
        // name it was told to stop at and the name it has already entered are the declaration's, and
        // asking the type for one beside the reading is a second answer to that.
        TypeGuarantees.At here = guarantees.at(root, at);
        TypeSymbol name = here.name();
        if (name != null) {
            if (scope.stopAt().test(name)) {
                reader.stopped(path, root.type(), Stop.ASKED_TO_STOP);
                return;
            }
            // A name already entered was read where it was met, so reading it again would be the
            // same reading done twice — which costs, and which a reader that remembers what it was
            // asked would see twice.
            if (entered.contains(name)) {
                reader.stopped(path, root.type(), Stop.ALREADY_ENTERED);
                return;
            }
        }
        // What the declaration states is read whatever this walk was asked for; whether this reader
        // hears it is the scope's answer. A reader told to leave a declaration's clauses out was not
        // asked to lose any, so nothing is reported lost for them either.
        if (name == null || !scope.withoutClauses().test(name)) {
            if (here.coverage() instanceof TypeGuarantees.At.Coverage.Incomplete incomplete) {
                reader.lostAClause(path, incomplete.lost());
            }
            for (TypeGuarantee guarantee : here.here()) {
                reader.guaranteed(path, guarantee);
            }
        }
        // Said whether or not anything was read here, and never instead of it. Both are true of a
        // sum whose cases share a spread.
        if (here.handedOn() instanceof TypeGuarantees.At.HandedOn.ToAnotherReading) {
            reader.handedOn(path, root.type());
        }
        // Entered before anything under it is walked, so that the one name and the other stay
        // paired: a stop taken after entering would leave the name on the path with nothing to take
        // it off, and the next field of the same type would be passed over as one already read.
        if (name != null) {
            entered.add(name);
        }
        for (TypeGuarantees.At.Beneath under : here.beneath()) {
            // A position wearing a name is at a path of its own; a newtype's value is the same
            // position and keeps this one's, which is the rule a path walks by: wearing a name is
            // not being somewhere else.
            String there = under.field().isEmpty() ? path : under(path, under.field());
            walk(under.value(), there, at, depth + 1, scope, entered, reader);
        }
        if (name != null) {
            entered.remove(name);
        }
    }

    /** A field of the value at {@code path}. The root of a newtype's own reading is the value it
     * wraps, which is at no path of its own, so its fields are the first step there is. */
    static String under(String path, String field) {
        return path.isEmpty() ? field : path + "." + field;
    }
}
