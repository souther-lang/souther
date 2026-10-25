package souther.compiler.check;

import souther.compiler.core.Core;

import java.util.Objects;

/**
 * One statement of a declaration's invariant, as what it says rather than as how it was written.
 *
 * <p>What a reader downstream asks of a rule is what it states about which value, and the answer is
 * the same for a rule written out, the same rule reached through a helper and the same rule written
 * as the denial of its opposite: a binding is where a reading's environment changes and states
 * nothing of its own, and a denial is carried to the leaves and spent where the comparison is read.
 * A reader handed the tree instead reads those forms as three shapes, and two of them as shapes it
 * has no word for.
 *
 * <p><b>A statement this reading made nothing of is still a statement.</b> Left out, a conjunct
 * stating two rules where one was recognised would come back as a conjunct stating one — and a
 * consumer that acts on what it was handed would act on half a rule. So the arm is here, carrying
 * its identity and nothing else.
 */
public sealed interface InvariantStatement {

    /** Which statement of which conjunct of which clause this is. */
    InvariantStatementId id();

    /**
     * A comparison, with the polarity the clause held it under and the side it was written on
     * already spent.
     *
     * <p>What is left is a claim about two values in that order, so a reader has nothing to apply
     * and nothing to forget ({@link StatedComparison}).
     */
    record Compares(InvariantStatementId id, StatedComparison states) implements InvariantStatement {

        public Compares {
            Objects.requireNonNull(id, "a comparison a reading arrived at is some statement");
            Objects.requireNonNull(states, "a statement that compares states a comparison");
        }
    }

    /**
     * An operation the representation kept standing, applied to the values the rule is about.
     *
     * <p>Which operation a rule is written in terms of is what a mapping onto something outside the
     * language is made of, and it survives because the representation these are read in keeps the
     * language's own operations as calls ({@link InliningPolicy#DISCHARGE}).
     *
     * <p>Stated and never denied. What holds where an operation does not is not that operation, and
     * a reader given the call under a polarity would have to work out what the denial of it states —
     * which is the question the polarity was spent to stop being asked. A rule under a denial that
     * no comparison was read from is {@link Unread}.
     */
    record Applies(InvariantStatementId id, Core.PreservedCall call) implements InvariantStatement {

        public Applies {
            Objects.requireNonNull(id, "an operation a rule is written in terms of is some statement");
            Objects.requireNonNull(call, "a statement that applies an operation applies one");
        }
    }

    /**
     * A rule asking a map for an entry under a key, and where it does the value under it
     * ({@link EntryHeld}).
     *
     * <p>Stated and never denied, for the reason an operation is: a map without the entry is not
     * the rule's denial but the rule's absence.
     */
    record HoldsAnEntry(InvariantStatementId id, EntryHeld.Stated held)
            implements InvariantStatement {

        public HoldsAnEntry {
            Objects.requireNonNull(id, "a rule asking a map for an entry is some statement");
            Objects.requireNonNull(held, "and it asks for one");
        }
    }

    /**
     * A rule saying the elements of a list standing at one case of a field add up to what those at
     * another case do ({@link SidesBalanced}).
     */
    record BalancesSides(InvariantStatementId id, SidesBalanced.Stated balanced)
            implements InvariantStatement {

        public BalancesSides {
            Objects.requireNonNull(id, "a rule balancing the sides of a list is some statement");
            Objects.requireNonNull(balanced, "and it balances some");
        }
    }

    /**
     * A statement this reading recognised and made nothing of.
     *
     * <p>Not a rule that states nothing, and the difference is what a consumer acts on: from "this
     * reading has no form for it" follows that whatever the consumer would have done about it is not
     * done, and from "it states nothing" follows something about the author's model that is not
     * true.
     */
    record Unread(InvariantStatementId id, boolean denies) implements InvariantStatement {

        public Unread {
            Objects.requireNonNull(id, "a statement nothing was made of is still some statement");
        }

        /** A statement nothing was made of, and which is not the denial of one that would have
         *  been. */
        public Unread(InvariantStatementId id) {
            this(id, false);
        }
    }

    // `denies` is whether the statement is the denial of a rule of a kind some consumer builds for
    // (a map holding an entry, a list balanced between two cases of a field): written under a
    // denial it is read as nothing, and what is built for the rules beside it is built without
    // knowing it asks the opposite. Said apart from the statements this reading has no form for,
    // which are most comparisons and ask nothing of what is built.
}
