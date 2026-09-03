package souther.compiler.check;

import souther.compiler.inputs.BlockReason;
import souther.compiler.values.AdmittedPlan;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * What one reading of a clause states about the strings at one position.
 *
 * <p>Two answers because the reading of such a rule has two outcomes a later reader has to tell
 * apart: it worked out which strings the rule admits, or it did not. Which position the rule is
 * about is settled either way and is not here — it is what this is filed under, so a rule whose
 * text nothing worked out is still a rule about the position it names.
 *
 * <p><b>Which is why the plan is not carried on its own.</b> What a reading leaves where it worked
 * nothing out is every value ({@link souther.compiler.values.ValueSet#ANY}), and that is what a
 * position nothing was read about holds — the same value for two opposite facts. Carried as the
 * plan alone, a rule this could not read arrived at the reading of where the values stop looking
 * like a rule that admits every string, and a run would have been read off it.
 *
 * <p><b>A branch's answer and not a clause's.</b> Which strings a part admits is what its own
 * branch of every choice in it leaves, and so is whether they were worked out: a branch nobody can
 * take is dropped, and what it could not read goes with it. Read off the clause as a whole, a rule
 * this could not read in a branch that turns out impossible would hide the run the branch that
 * stands does state. So these compose where the readings do.
 */
sealed interface StringRestriction {

    /**
     * The rule admits what the plan admits.
     *
     * <p>The plan and not the set. Which strings a rule leaves is a machine somebody has to pay
     * for, and whether one is ever made is settled under the allowance of whoever asks — held as
     * the set, every rule about a string would be a machine made while the clause was read, for a
     * question nobody may go on to ask.
     */
    record Admitting(AdmittedPlan plan) implements StringRestriction {

        public Admitting {
            if (plan == null) {
                throw new IllegalArgumentException("a rule that was read admits something");
            }
        }
    }

    /**
     * The rule is one of these and what it admits was not worked out, and what stopped the reading.
     *
     * <p>The reason travels because a reader of this decides more than whether to ask where the
     * values stop. Whether the rule states a boundary at all is undecided here — not answered no —
     * and what a report says about a question nothing settled is the reason it was not settled. The
     * fact itself is the recognition's ({@link StringPredicates.Reading}); this is that one fact
     * said in the words a rule left unread is written down in.
     */
    record NotKnown(BlockReason.RuleReadingStopped why) implements StringRestriction {

        public NotKnown {
            if (why == null) {
                throw new IllegalArgumentException("a reading that stopped was stopped by something");
            }
        }
    }

    /**
     * What two readings of one position come to, held together or as a choice between them.
     *
     * <p>The same rule either way, because what is being asked is what the strings at the position
     * are and a plan already knows how to be met and joined. Not knowing wins: a part admitting what
     * one reading leaves together with what another leaves, where the second was not worked out,
     * admits something this cannot name — and what would be read off the half that was read is a run
     * of a set the rule does not have, which is what tells a boundary from a distinction.
     *
     * @param one the reading on one side, or null where that side states no rule about this
     *            position — which leaves every string standing there
     */
    static StringRestriction over(StringRestriction one, StringRestriction other, boolean met) {
        if (one instanceof NotKnown it) {
            return it;
        }
        if (other instanceof NotKnown it) {
            return it;
        }
        AdmittedPlan here = one instanceof Admitting it ? it.plan() : AdmittedPlan.ANY;
        AdmittedPlan there = other instanceof Admitting it ? it.plan() : AdmittedPlan.ANY;
        return new Admitting(met
                ? AdmittedPlan.meeting(java.util.List.of(here, there))
                : AdmittedPlan.joining(java.util.List.of(here, there)));
    }

    /** The same over every position either of them states a rule about. */
    static Map<FactSubject, StringRestriction> over(Map<FactSubject, StringRestriction> these,
                                                    Map<FactSubject, StringRestriction> those,
                                                    boolean met) {
        if (those.isEmpty()) {
            return these;
        }
        if (these.isEmpty()) {
            return those;
        }
        Set<FactSubject> named = new LinkedHashSet<>(these.keySet());
        named.addAll(those.keySet());
        Map<FactSubject, StringRestriction> out = new LinkedHashMap<>();
        named.forEach(position ->
                out.put(position, over(these.get(position), those.get(position), met)));
        return Map.copyOf(out);
    }
}
