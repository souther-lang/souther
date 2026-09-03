package souther.compiler.check;

import souther.compiler.values.AdmittedPlan;

/**
 * What one part of a clause states about the strings at one position.
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
 * <p>Why the reading stopped is not here either. That is the accounting's, said once where the rule
 * was read, and a second copy of it travelling beside this would be a second answer to a question
 * that has an owner.
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
     * The rule is one of these and what it admits was not worked out.
     *
     * <p>A pattern written more deeply than the subset read, a text composed out of something this
     * could not fold. What follows is that nothing is known about where the values stop — not that
     * they stop nowhere.
     */
    record NotKnown() implements StringRestriction {}

    /**
     * The two of them together, which is what a part holding both comes to.
     *
     * <p>Not knowing wins. A part whose strings are the ones one leaf admits together with the ones
     * another leaf admits, where the second was not read, admits something this cannot name — and a
     * run read off the half that was read would be a run of a set the rule does not have.
     */
    static StringRestriction and(StringRestriction one, StringRestriction other) {
        if (one == null) {
            return other;
        }
        if (other == null) {
            return one;
        }
        return one instanceof NotKnown || other instanceof NotKnown ? new NotKnown() : one;
    }

    /**
     * The positions a clause states a rule about the strings of, told apart by whether the rule was
     * read to the strings it admits.
     *
     * <p>A fact about the clause and the same in every branch of a choice in it, which is why it is
     * worked out where the clause is walked and handed to each branch. What each branch admits at
     * one of those positions is the branch's own and is read there.
     *
     * @param read    the positions every such rule about which was read to its strings
     * @param notRead the positions some such rule about which was not. A position is in one of the
     *                two and never both: a part admitting what one rule leaves together with what
     *                another leaves, where the second was not read, admits something this cannot
     *                name
     */
    record Found(java.util.Set<FactSubject> read, java.util.Set<FactSubject> notRead) {

        static final Found NONE = new Found(java.util.Set.of(), java.util.Set.of());

        public Found {
            read = java.util.Set.copyOf(read);
            notRead = java.util.Set.copyOf(notRead);
        }

        /** Whether the clause states no rule about the strings anywhere. */
        boolean isEmpty() {
            return read.isEmpty() && notRead.isEmpty();
        }

        /** Every position, whichever of the two it is in. */
        java.util.Set<FactSubject> anywhere() {
            java.util.Set<FactSubject> out = new java.util.LinkedHashSet<>(read);
            out.addAll(notRead);
            return out;
        }
    }
}
