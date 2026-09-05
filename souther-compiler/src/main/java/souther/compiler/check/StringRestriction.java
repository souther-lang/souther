package souther.compiler.check;

import souther.compiler.inputs.BlockReason;
import souther.compiler.values.AdmittedPlan;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
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
    record NotKnown(List<BlockReason.RuleReadingStopped> why) implements StringRestriction {

        public NotKnown {
            if (why.isEmpty()) {
                throw new IllegalArgumentException("a reading that stopped was stopped by something");
            }
            why = List.copyOf(why);
        }

        NotKnown(BlockReason.RuleReadingStopped one) {
            this(List.of(one));
        }

        /**
         * Both of them, each reason once and in the order the clause writes them.
         *
         * <p>Every reason and not the first. Two branches of one choice can be stopped by two
         * different things — one written more deeply than this reads, one written in a form it does
         * not enter — and those go out under two different words. Keeping one, which of them a
         * reader is shown would turn on which branch the author wrote first.
         */
        NotKnown and(NotKnown other) {
            List<BlockReason.RuleReadingStopped> out = new ArrayList<>(why);
            other.why().stream().filter(each -> !out.contains(each)).forEach(out::add);
            return new NotKnown(out);
        }
    }

    /**
     * What a reading that states no rule about the strings at a position leaves there.
     *
     * <p>Every string, and known to be: a reading says nothing about a position by not writing
     * about it, which is a fact about the clause and not something it could not work out. Written as
     * an absence and read as one, the two operations below would each need a case for it — and the
     * one that got a case was right at the first level and wrong as soon as its answer was composed
     * again.
     */
    StringRestriction EVERY_STRING = new Admitting(AdmittedPlan.ANY);

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
        // A reading that states no rule about the strings here leaves every string standing, and
        // that is a value like any other. Lifted first, so that everything below is one algebra
        // over three kinds of answer rather than an algebra with a case for an absence — a case is
        // what makes the first level right and the composition of its answer wrong.
        StringRestriction here = one == null ? EVERY_STRING : one;
        StringRestriction there = other == null ? EVERY_STRING : other;
        // The laws about what is known, before what is not. Every string absorbs a choice and is
        // the identity of a conjunction, and nothing at all absorbs a conjunction — each of them
        // settles the pair whether or not the other side was worked out, so a reading that stopped
        // does not make the answer unknown where the law already gives it.
        if (met) {
            if (admits(here, AdmittedPlan.Nothing.class)
                    || admits(there, AdmittedPlan.Nothing.class)) {
                return new Admitting(AdmittedPlan.NONE);
            }
            if (admits(here, AdmittedPlan.Everything.class)) {
                return there;
            }
            if (admits(there, AdmittedPlan.Everything.class)) {
                return here;
            }
        } else if (admits(here, AdmittedPlan.Everything.class)
                || admits(there, AdmittedPlan.Everything.class)) {
            return EVERY_STRING;
        }
        // And then what neither law reaches. A pair one side of which was not worked out admits
        // something this cannot name, and a run read off the side that was read is a run of a set
        // the rule does not have.
        if (here instanceof NotKnown a && there instanceof NotKnown b) {
            return a.and(b);
        }
        if (here instanceof NotKnown a) {
            return a;
        }
        if (there instanceof NotKnown b) {
            return b;
        }
        AdmittedPlan first = ((Admitting) here).plan();
        AdmittedPlan second = ((Admitting) there).plan();
        return new Admitting(met
                ? AdmittedPlan.meeting(List.of(first, second))
                : AdmittedPlan.joining(List.of(first, second)));
    }

    /**
     * Whether {@code said} is known to admit what {@code shape} names, read off the plan and
     * nothing built.
     *
     * <p>A plan written as every value or as none says so by being that shape. One written as a
     * pattern may come to either and is not read as one here: what would settle it is making the
     * machine, and the laws above are the ones that hold without making anything. Where a plan
     * that would have absorbed goes unrecognised, the answer falls through to the algebra over the
     * plans, which normalises the same absorbers itself.
     */
    private static boolean admits(StringRestriction said, Class<? extends AdmittedPlan> shape) {
        return said instanceof Admitting it && shape.isInstance(it.plan());
    }

    /**
     * The same over every position either of them states a rule about.
     *
     * <p>Every position and no shortcut for an empty side. What one reading says nothing about is
     * every string on that side, and for a choice that absorbs whatever the other says — so a side
     * with nothing in it is exactly where the answer changes, and taking the other side whole is
     * the one case that must not be waved through.
     *
     * <p>A position stays here whichever way it came out, because the key is also what says this
     * clause writes about the strings at it. Dropped where the answer came to every string, a rule
     * about a position would stop being a rule about it.
     */
    static Map<FactSubject, StringRestriction> over(Map<FactSubject, StringRestriction> these,
                                                    Map<FactSubject, StringRestriction> those,
                                                    boolean met) {
        if (these.isEmpty() && those.isEmpty()) {
            return Map.of();
        }
        Set<FactSubject> named = new LinkedHashSet<>(these.keySet());
        named.addAll(those.keySet());
        Map<FactSubject, StringRestriction> out = new LinkedHashMap<>();
        named.forEach(position ->
                out.put(position, over(these.get(position), those.get(position), met)));
        // The order the positions were read in, kept: what is written out of these reaches a
        // report, and the iteration order of an immutable copy is salted once per run.
        return Collections.unmodifiableMap(out);
    }
}
