package souther.compiler.check;

import souther.compiler.core.Core;

import java.util.ArrayList;
import java.util.List;

/**
 * A value that is one of several: which several, what it asks to decide between them, and what
 * decides each one.
 *
 * <p>One question with one answer. It was asked in four places and each wrote its own list — the
 * search for a split in a value position, the reading of what a split's arms are, the test of
 * whether a node is one, and the recording of what a value was computed from. All four said
 * {@code if} and {@code match}, and none said an attempted construction, which answers what it
 * built where its invariant held and what it departs with where it did not. So an attempt was a
 * value with a name and nothing recorded about the values it is one of, which is what
 * {@link Derivation.Chosen} was made for, standing under a third spelling.
 *
 * <p><b>What decides an arm is named here and read nowhere.</b> {@link Decides} is the node that
 * decides — a condition and which way it went, a case of a sum, an attempt that held or departed —
 * and this puts no interpretation on it. What such a node <em>settles</em> is a different question,
 * needing an environment to settle it in, and it has its own reader ({@link PathEngine}) which not
 * every caller here can reach (#973). Keeping the two apart is what lets a reader that only wants
 * the values have them, while a reader that wants more is handed the node rather than going back to
 * the tree to find it for itself.
 *
 * <p>Which is also where a reader is made to stop. {@link Kind} on its own stops nobody: it is a
 * label, and a kind nothing produces is inert — adding one and answering for it compiles, and
 * should. What a new choice really needs is a case in {@link #of}, and then a way for each of its
 * arms to be decided. So the sum to switch over is {@link Decides}, which is what a reader has to
 * interpret to do anything at all, and a new way of deciding an arm fails exhaustiveness at every
 * such reader until it is handled.
 *
 * <p>That distinction is this class's own history. The forcing was first put on {@link Kind}, at a
 * reader that did not open anything, and a kind could be declared a split while no reader opened
 * one — a tripwire that read as holding, which is worse than none, since the words claimed it.
 */
record Choice(Kind kind, Core asked, List<Arm> arms) {

    /** What is being chosen between, for a reader whose answer differs by which it is. Named after
     * what decides the choice rather than after the syntax, since that is what a reader wanting more
     * than the values is asking about. */
    enum Kind {

        /** A condition decides, and the values are its two branches. */
        A_CONDITION,

        /** Which case the scrutinee is decides, and the values are the arms' bodies. */
        A_CASE,

        /** Whether a construction's invariant held decides, and the values are what is answered
         * where it did and where it did not. */
        AN_ATTEMPT
    }

    /** One value a choice may answer, and the node that decides it is the one. */
    record Arm(Core answers, Decides decidedBy) {}

    /**
     * What decides one arm, as the node that decides it.
     *
     * <p>Sealed, and one arm per way an arm is chosen rather than one per kind of choice: an attempt
     * that held and an attempt that departed are decided by different things and settle different
     * things, so a reader treating them alike would have to tell them apart again.
     */
    sealed interface Decides {

        /** The condition held, or it did not. */
        record ACondition(Core cond, boolean holding) implements Decides {}

        /** The scrutinee is one of the cases this arm names. The scrutinee travels with it: what an
         * arm binds is the value already there, refined to the case. */
        record ACase(Core.Case arm, Core scrutinee) implements Decides {}

        /** The attempt's invariant held, so the value was built and its {@code as} name stands for
         * it. */
        record ItWasBuilt(Core.IfConstructed attempt) implements Decides {}

        /** The attempt's invariant did not hold, so this departure was taken and nothing was
         * built. */
        record ItDeparted(Core.IfConstructed attempt, Core.ElseArm on) implements Decides {}
    }

    Choice {
        arms = List.copyOf(arms);
        if (arms.isEmpty()) {
            throw new IllegalArgumentException(kind + " is a value that is one of several and it was"
                    + " given none to be one of");
        }
    }

    /** The values one of which this answers, in the order the arms stand in. */
    List<Core> alternatives() {
        return arms.stream().map(Arm::answers).toList();
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
            case Core.If iff -> new Choice(Kind.A_CONDITION, iff.cond(), List.of(
                    new Arm(iff.then(), new Decides.ACondition(iff.cond(), true)),
                    new Arm(iff.els(), new Decides.ACondition(iff.cond(), false))));
            case Core.Match m -> new Choice(Kind.A_CASE, m.scrutinee(), m.cases().stream()
                    .map(c -> new Arm(c.body(), new Decides.ACase(c, m.scrutinee())))
                    .toList());
            case Core.IfConstructed ic ->
                    new Choice(Kind.AN_ATTEMPT, ic.construct(), attempted(ic));
            case null, default -> null;
        };
    }

    /** What an attempt answers: the value built where its invariant held, and what is taken where it
     * did not — one departure per clause the attempt names, and each of them a value of its own. */
    private static List<Arm> attempted(Core.IfConstructed ic) {
        List<Arm> out = new ArrayList<>();
        out.add(new Arm(ic.then(), new Decides.ItWasBuilt(ic)));
        ic.els().forEach(arm -> out.add(new Arm(arm.body(), new Decides.ItDeparted(ic, arm))));
        return out;
    }
}
