package souther.compiler.check;

import souther.compiler.core.Core;

import java.util.ArrayList;
import java.util.List;

/**
 * A value that is one of several, and which several.
 *
 * <p>One question with one answer. It was asked in four places and each wrote its own list —
 * {@link InvariantChecker}'s search for a split in a value position, its reading of what a split's
 * arms are, its test of whether a node is one, and {@link Terms}' recording of what a value was
 * computed from. All four said {@code if} and {@code match}, and none of them said an attempted
 * construction, which answers one of several as plainly as either. So a value written as an attempt
 * had a name and nothing recorded about the values it is one of — which is the whole of what #964
 * was, left standing under a third spelling.
 *
 * <p>Written here as {@link Core} and nothing else. What choosing an arm settles is a separate
 * question and a heavier one: it needs an environment to settle it in, and its answer is different
 * for each kind of choice — a condition, a case of a sum, an invariant that held. That question has
 * its own reader ({@link InvariantChecker}'s {@code Choosing}) which cannot be asked from here, and
 * the day it is asked from both places it goes where this is rather than beside it (#973). Keeping
 * the two apart is what lets a reader that only needs the alternatives have them.
 *
 * <p>{@link Kind} is what makes a reader that needs more than the alternatives say so. A reader
 * switching over it exhaustively is one a new kind of choice stops at, which is the point: a choice
 * added without a decision recorded at each such reader is how this came apart the first time.
 */
record Choice(Kind kind, List<Core> alternatives) {

    /** What is being chosen between, for a reader whose answer differs by which it is. Named after
     * what decides the choice rather than after the syntax, since that is what a reader wanting more
     * than the alternatives is asking about. */
    enum Kind {

        /** A condition decides, and the alternatives are its two branches. */
        A_CONDITION,

        /** Which case the scrutinee is decides, and the alternatives are the arms' bodies. */
        A_CASE,

        /** Whether a construction's invariant held decides, and the alternatives are what is
         * answered where it did and where it did not. */
        AN_ATTEMPT
    }

    Choice {
        alternatives = List.copyOf(alternatives);
        if (alternatives.isEmpty()) {
            throw new IllegalArgumentException(kind + " is a value that is one of several and it was"
                    + " given none to be one of");
        }
    }

    /**
     * The choice {@code e} is, or null where {@code e} answers one value.
     *
     * <p>Read off the node and not off what stands in it. An arm that is itself a choice is a choice
     * standing in an arm, which is what a reader of the arms finds when it reads them; flattening
     * the two here would answer about a value nothing is written at.
     */
    static Choice of(Core e) {
        return switch (e) {
            case Core.If iff -> new Choice(Kind.A_CONDITION, List.of(iff.then(), iff.els()));
            case Core.Match m ->
                    new Choice(Kind.A_CASE, m.cases().stream().map(Core.Case::body).toList());
            case Core.IfConstructed ic -> new Choice(Kind.AN_ATTEMPT, departures(ic));
            case null, default -> null;
        };
    }

    /** What an attempt answers: the value built where its invariant held, and what is taken where it
     * did not — one departure per clause the attempt names, and each of them a value of its own. */
    private static List<Core> departures(Core.IfConstructed ic) {
        List<Core> out = new ArrayList<>();
        out.add(ic.then());
        ic.els().forEach(arm -> out.add(arm.body()));
        return out;
    }
}
