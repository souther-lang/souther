package souther.compiler.examples;

import souther.compiler.observe.ObservedValue;

import java.util.Locale;

/**
 * What a bound implementation answered for a row's inputs, held to what the behavior declares of
 * what it answers — and to nothing the row records.
 *
 * <p>A different oracle from {@link RowEvaluation}'s, not a different world. {@code evaluate} holds
 * an answer to the declaration <em>and</em> to the value somebody wrote out; this holds it to the
 * declaration alone. The two part inside one world as readily as across two: a behavior that states
 * nothing about the order of what it answers admits a page the recorded one is a permutation of, and
 * that answer keeps the declaration while differing from the record.
 *
 * <p>Where the two most often part is a world the rows were not recorded in — a shared database, a
 * snapshot, a seed of another size. There what was written out is no longer the answer and what the
 * behavior states still is. That is what this face is for, and it is a use of the distinction rather
 * than the distinction itself.
 *
 * <p>An observation and not a verdict, for the reason {@link StandinObservation} is one: whether an
 * arm fails a build is a policy, and a policy is the consumer's. Nothing here carries a severity.
 */
public sealed interface ContractObservation {

    /**
     * What to say about this observation, in one line per thing said.
     *
     * <p>The language is handed in and not picked here, for the reason
     * {@link RowEvaluation#shown(Locale)} takes one: what answers a reader has to say which reader,
     * and that is the consumer.
     */
    String shown(Locale locale);

    /**
     * No clause of the behavior was shown to be broken by what the implementation answered.
     *
     * <p><strong>This does not say that every clause bore on the answer.</strong> A clause is
     * vacuous for an input it says nothing about — {@code readArticles}'s rule about what a page
     * holds says nothing about a query filtering on something the page does not carry — and such a
     * row arrives here having proved nothing. What is claimed is the absence of a violation, which
     * is what the check answers, and the name says that and no more.
     *
     * <p>Not a record, and alone among the arms in that. The other three are what they carry: an
     * observation of a finite number of parts, worth taking apart. This one carries nothing
     * <em>yet</em> — which clauses bore on the answer is the evidence it is to hold — and a record
     * would put the absence into the API twice over: as a canonical constructor callers may write
     * and a later component would break, and as an equality over instances this is not yet ready to
     * define. So the arm is a class, its constructor is this package's, and nothing is promised
     * about how many of them there are.
     */
    final class NoClauseWasBroken implements ContractObservation {

        NoClauseWasBroken() {}

        @Override
        public String shown(Locale locale) {
            return "no clause was broken";
        }

        @Override
        public String toString() {
            return "NoClauseWasBroken";
        }
    }

    /**
     * A clause did not hold of what the implementation answered.
     *
     * @param why      what the clause said when it did not hold, in the words the runtime writes
     *                 about one
     * @param answered what the implementation answered, so a reader is told what broke it and not
     *                 only that something did
     */
    record Broken(String why, ObservedValue answered) implements ContractObservation {

        public Broken {
            if (why == null) {
                throw new IllegalArgumentException("a broken clause said something");
            }
        }

        @Override
        public String shown(Locale locale) {
            return "a clause did not hold: " + why
                    + System.lineSeparator() + "  answered: " + answered;
        }
    }

    /**
     * The behavior states nothing, so this row held the implementation to nothing.
     *
     * <p>An arm and not a quiet yes. A suite written over a behavior with no {@code ensures} would
     * otherwise be green while asserting only that the call did not throw, and say so to nobody.
     * What the author does about it — write the clause, or leave the behavior out with
     * {@link BoundExamples#behaviorsStatingContracts()} — is theirs; being told is not.
     *
     * @param behavior which behavior states nothing, for a suite over several
     */
    record NothingStated(String behavior) implements ContractObservation {

        @Override
        public String shown(Locale locale) {
            return "`" + behavior + "` states nothing of what it answers,"
                    + " so this row held the implementation to nothing";
        }
    }

    /**
     * No answer was held to anything.
     *
     * <p>What keeps the other three meaning that one was. An implementation that aborted, or an
     * answer that could not be read in the classes the check reads, has not kept the declaration and
     * has not broken it.
     *
     * <p>Reuses {@link StandinObservation.Reason}: how far an observation got is the same question
     * whichever of the two faces asked it, and a second vocabulary saying the same six things would
     * be a second answer to it.
     */
    record Unobserved(StandinObservation.Reason why) implements ContractObservation {

        @Override
        public String shown(Locale locale) {
            return "nothing was held to the declaration: " + why.said();
        }
    }
}
