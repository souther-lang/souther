package souther.compiler.inputs;

/**
 * What became of one placement at one of the places the name it was written at reaches.
 *
 * <p>Three, and what separates them is who answered rather than how much was achieved. A filing is
 * this compiler having somewhere to put the rule. A refusal is the reading holding to something it
 * already said about the model — nothing is missing and nobody is owed anything. Only the third is
 * this compiler coming up short, and it is the only one a measurement may not be called complete
 * over.
 *
 * <p><b>Every one of them is observed.</b> A refusal is made from what the walk wrote down about the
 * case, and cannot be made from anything else; the reason a name reached nowhere is the reason the
 * reading gave at the position it stopped at. Nothing here is concluded from an artifact being
 * absent, which is the one way a report comes to name a cause nobody established.
 */
public sealed interface PlacementOutcome {

    /** The rule has a position to be about. */
    record Filed(PositionId at) implements PlacementOutcome {

        public Filed {
            if (at == null) {
                throw new IllegalArgumentException("a filing is at a position");
            }
        }
    }

    /**
     * The name reaches this case, and the reading had already said no row is written under it.
     *
     * <p>Not a shortfall and not a gap. A rule asking something of a case that holds nothing, or of
     * one the rules leave no value of, is answered by the reading it was asked against — and a
     * measurement is as complete with one of these in it as without.
     *
     * <p><b>Made only from what the walk observed</b> ({@link NameReach.BranchNotEntered}), so there
     * is no way to write one from a name having failed to reach somewhere. Which is the whole of the
     * difference from the arm below: told apart by a caller's judgement, the two would be one
     * reader's guess about which had happened.
     */
    record Refused(NameReach.BranchNotEntered observed) implements PlacementOutcome {

        public Refused {
            if (observed == null) {
                throw new IllegalArgumentException(
                        "a refusal is the reading's, and is made from what it said");
            }
        }
    }

    /**
     * The name reaches no position, and this is what the reading said where it stopped.
     *
     * <p>What a measurement may not be called complete over. Something was written about the model
     * and this compiler has nowhere to put it, so what a report owes its reader is this and not the
     * silence that would otherwise stand in the same place.
     */
    record Unresolved(Reason why) implements PlacementOutcome {

        public Unresolved {
            if (why == null) {
                throw new IllegalArgumentException("a name that reached nowhere did so for a reason");
            }
        }
    }

    /** Why a name reached no position. */
    sealed interface Reason {

        /**
         * The reading stopped at the position the name was being followed from, and said so there.
         *
         * <p>Carried from the position rather than worked out here: which limit stopped a reading is
         * that reading's answer, and a second opinion about it would be a report naming a cause the
         * walk never gave.
         *
         * @param at  the last position the name was followed to
         * @param why what the reading of that position was left with
         */
        record TheReadingStoppedThere(PositionId at, BlockReason.AboutThePosition why)
                implements Reason {

            public TheReadingStoppedThere {
                if (at == null || why == null) {
                    throw new IllegalArgumentException("a reading stopped somewhere, and at something");
                }
            }
        }

        /**
         * The reading reached the position the name was followed from, went on down, and put nothing
         * of that name anywhere.
         *
         * <p>What is left when nothing else answered, and it says that and only that. A name a rule
         * wrote that no position answers to is a rule this compiler cannot hold against any row, and
         * an author is owed the name rather than a guess about why it is not there.
         *
         * @param at    the last position the name was followed to
         * @param named the step of the name that reached nothing
         */
        record NothingOfThatNameThere(PositionId at, String named) implements Reason {

            public NothingOfThatNameThere {
                if (at == null || named == null) {
                    throw new IllegalArgumentException("a name that is nowhere is still a name");
                }
            }
        }

    }
}
