package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.HashSet;
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
     * How far a reader is asking this walk to go.
     *
     * <p>Not one number for everybody. What a walk over a body can afford to read of a parameter is
     * a cost bound; what a construction has to satisfy has no depth at all, since a rule four
     * records down refuses the outermost value exactly as one on the top does.
     *
     * @param depth           how many positions down to read
     * @param stopAt          names this reader is supposing hold values whatever is written under
     *                        them, so nothing under one of them is read
     * @param withoutClauses  names whose own clauses this reader asked to leave out, what is under
     *                        them still being read
     */
    record Scope(int depth, Predicate<TypeSymbol> stopAt, Predicate<TypeSymbol> withoutClauses) {

        /** Every rule down to {@code depth} positions, wherever it is written. */
        static Scope asFarAs(int depth) {
            return new Scope(depth, _ -> false, _ -> false);
        }
    }

    /** Told what was read, and where the reading stopped. */
    interface Reader {

        /** What the declaration at {@code path} guarantees of the value there. */
        void guaranteed(String path, TypeGuarantee guarantee);

        /** Where the walk went no further, and what stood there. */
        default void stopped(String path, Type type, Stop why) {}

        /** That a declaration at {@code path} writes clauses this reading could not state, so what
         * they were about is not among what was handed over. */
        default void lostAClause(String path) {}
    }

    /** Why a walk went no further. */
    enum Stop {

        /** As far down as the reader asked to be taken. Not a limit on the model: a rule four
         * records down refuses the outermost construction exactly as one on its own fields does. */
        PAST_THE_DEPTH,

        /** Nothing is declared here that could hold a rule about every value standing at it: a
         * container or an optional, a type nothing is written under, or a choice between
         * declarations, whose rules are about values of one case and not about every value here. */
        NOTHING_DECLARED,

        /** A name the reader is supposing holds values, so what is under it says nothing here. */
        ASKED_TO_STOP,

        /** Met already on the way down, and read where it was met. A record holding one of its own
         * kind stops here and nothing is short of anything for it. */
        ALREADY_ENTERED,

        /** A declaration names a position the walk could find no value for. */
        NO_VALUE_THERE
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
        if (depth > scope.depth()) {
            reader.stopped(path, root.type(), Stop.PAST_THE_DEPTH);
            return;
        }
        if (!(root.type() instanceof Type.Ref ref)) {
            // Nothing here is named, so there is nothing this walk could have been told to stop at
            // and nothing to record as entered.
            reader.stopped(path, root.type(), Stop.NOTHING_DECLARED);
            return;
        }
        // Asked of the name and before the reading, because being told to stop at a name is this
        // walk's business and says nothing about what the declaration states.
        if (scope.stopAt().test(ref.name())) {
            reader.stopped(path, root.type(), Stop.ASKED_TO_STOP);
            return;
        }
        if (!(guarantees.at(root, at) instanceof TypeGuarantees.At.Declared here)) {
            reader.stopped(path, root.type(), Stop.NOTHING_DECLARED);
            return;
        }
        // Entered before anything under it is walked, so that the one name and the other stay
        // paired: a stop taken after entering would leave the name on the path with nothing to take
        // it off, and the next field of the same type would be passed over as one already read.
        if (!entered.add(here.name())) {
            reader.stopped(path, root.type(), Stop.ALREADY_ENTERED);
            return;
        }
        // What the declaration states is read whatever this walk was asked for; whether this reader
        // hears it is the scope's answer. A reader told to leave a declaration's clauses out was not
        // asked to lose any, so nothing is reported lost for them either.
        if (!scope.withoutClauses().test(here.name())) {
            if (!here.everyClauseStated()) {
                reader.lostAClause(path);
            }
            for (TypeGuarantee guarantee : here.guarantees()) {
                reader.guaranteed(path, guarantee);
            }
        }
        for (TypeGuarantees.At.Beneath under : here.beneath()) {
            // A position wearing a name is at a path of its own; a newtype's value is the same
            // position and keeps this one's, which is the rule a path walks by: wearing a name is
            // not being somewhere else.
            String there = under.field().isEmpty() ? path : under(path, under.field());
            if (under.value() == null) {
                reader.stopped(there, under.type(), Stop.NO_VALUE_THERE);
            } else {
                walk(under.value(), there, at, depth + 1, scope, entered, reader);
            }
        }
        entered.remove(here.name());
    }

    /** A field of the value at {@code path}. The root of a newtype's own reading is the value it
     * wraps, which is at no path of its own, so its fields are the first step there is. */
    static String under(String path, String field) {
        return path.isEmpty() ? field : path + "." + field;
    }
}
