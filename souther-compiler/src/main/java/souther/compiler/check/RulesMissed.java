package souther.compiler.check;

/**
 * Why a rule written about a value reached no reading here.
 *
 * <p>What {@link InvariantChecker.Gathering#missed} used to say with a {@link
 * InvariantChecker.Borne} and a path. That pair says what a stop costs a construction and where it
 * happened, and says nothing about what stopped — so the six ways a rule goes ungathered arrived at
 * the far end as one set of paths, and anything asking a question the pair does not answer had
 * nothing to read.
 *
 * <p>Which is a question that turned up: whether a wider run of this compiler could get past it. A
 * walk stopped by the fields it can afford to seed is one a run allowed more of would go past, and
 * a clause nothing could type is not — and both were one word by the time a reason was built from
 * them.
 *
 * <p><b>The cause itself, and not a word for what it costs.</b> {@link #borne()} is derived here
 * rather than handed in beside it. A caller that passes both can pass a pair that disagrees, and
 * what a stop costs a construction follows from what the stop was — so it is read off the arm. The
 * one place the walk's own answer is written stays {@link PathEngine#leftBy}, which this asks.
 *
 * <p><b>And coarser downstream, on purpose.</b> Nothing outside this package is handed one of
 * these. What a reading records of itself is a {@link souther.compiler.values.UnreadReason}, at the
 * grain that reading can tell apart, and this is what that grain is chosen from rather than what it
 * is. A distinction worth keeping here need not be one a later vocabulary carries — what may not
 * happen is a distinction being lost before anybody has decided to lose it.
 */
public sealed interface RulesMissed {

    /** What a construction can no longer be refused by, which follows from what stopped. */
    InvariantChecker.Borne borne();

    /**
     * The walk over the value went no further, in one of the ways it can.
     *
     * <p>Holds the walk's own word rather than restating it. Which of them cost a construction
     * something is {@link PathEngine#leftBy}'s answer and is asked there, so this arm and that
     * table cannot come apart.
     */
    record WalkStopped(GuaranteeWalk.Stop why) implements RulesMissed {

        public WalkStopped {
            if (why == null) {
                throw new IllegalArgumentException("a walk that stopped stopped in some way");
            }
        }

        @Override
        public InvariantChecker.Borne borne() {
            return PathEngine.leftBy(why);
        }
    }

    /**
     * A clause of the declaration that nothing could type, so no reading ever saw which position it
     * was about.
     *
     * <p>Its own arm and not a walk that stopped: the walk arrived, and what was written here could
     * not be made into anything to read. A wider run meets it again.
     */
    record ClauseNotTyped() implements RulesMissed {

        @Override
        public InvariantChecker.Borne borne() {
            return InvariantChecker.Borne.BY_EVERY_VALUE;
        }
    }

    /**
     * A clause this reading held and could not state, which is not the same as one it never saw.
     *
     * <p>Said whatever stands under the position, because the clause was read and lost rather than
     * never reached — a reader answering for the clauses it was handed would otherwise answer for a
     * rule it never saw.
     */
    record ClauseLost() implements RulesMissed {

        @Override
        public InvariantChecker.Borne borne() {
            return InvariantChecker.Borne.BY_EVERY_VALUE;
        }
    }

    /**
     * The reading was told to stop at this position, and the declaration there writes clauses.
     *
     * <p>Not a walk that ran out of anything. What asked for the stop is the reach this reading was
     * made under, so it is the same on every run that asks the same question.
     */
    record PositionNotOpened() implements RulesMissed {

        @Override
        public InvariantChecker.Borne borne() {
            return InvariantChecker.Borne.BY_EVERY_VALUE;
        }
    }

    /**
     * A rule of the value this reading was asked to leave out.
     *
     * <p>Said once however many were left out: what is recorded is which position is short, and the
     * position is the value either way. Its own arm because nothing went wrong — the reading was
     * asked a narrower question, and the answer is short of exactly what it was not asked.
     */
    record ClauseNotAsked() implements RulesMissed {

        @Override
        public InvariantChecker.Borne borne() {
            return InvariantChecker.Borne.BY_EVERY_VALUE;
        }
    }

    /**
     * No reading of the declaration was made, so nothing was gathered anywhere in it.
     *
     * <p>Not a reading that found no rules and not one that stopped: a caller holding this holds it
     * because it chose not to read a declaration or had none to read. Its own arm for that reason —
     * a position nobody looked at and a position a look stopped short of are different things to
     * know, and both say the rules there went unread.
     */
    record NoReadingWasMade() implements RulesMissed {

        @Override
        public InvariantChecker.Borne borne() {
            return InvariantChecker.Borne.BY_EVERY_VALUE;
        }
    }

    /**
     * The reading fell over, so nothing about the value was gathered at all.
     *
     * <p>Said of the value itself, since nothing here knows which positions the rules were about.
     * Its own arm because it is the one that is about no rule and no walk: what happened is that
     * this compiler raised something reading a model that compiles.
     */
    record ReadingFellOver() implements RulesMissed {

        @Override
        public InvariantChecker.Borne borne() {
            return InvariantChecker.Borne.BY_EVERY_VALUE;
        }
    }
}
