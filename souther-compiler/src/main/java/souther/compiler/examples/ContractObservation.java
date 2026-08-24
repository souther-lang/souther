package souther.compiler.examples;

import souther.compiler.observe.ObservedValue;

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
     * What to say about this observation, for a consumer building an assertion message.
     *
     * <p>Takes no language, and that is the difference from {@link RowEvaluation#shown(java.util.Locale)}
     * rather than an omission from it. That one renders <em>diagnostics</em>, which are what a
     * compile reports and are written in the catalogs the compiler ships; handing it a language is
     * how a reader picks one. Nothing here is a diagnostic. No compile reports that a clause held,
     * and a sentence in the catalog is one classified as either a rule reported or a word said
     * beside one — these are neither.
     *
     * <p>So they are this face's own words, as {@link StandinObservation.Reason#said()}'s are, and
     * taking a language only to ignore it would promise a choice that is not there.
     */
    String shown();

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
        public String shown() {
            return "no clause of the behavior was broken by what was answered";
        }

        /** Its name. The other arms are records and carry what they hold; this one holds nothing
         *  yet, and the default would be an address. Read off the class rather than written out, so
         *  a rename does not leave the old word behind. */
        @Override
        public String toString() {
            return getClass().getSimpleName();
        }
    }

    /**
     * A clause did not hold of what the implementation answered.
     *
     * <p>What was answered is carried twice, and on purpose: structurally, for a reader that takes
     * it apart, and written the way a fixture writes a value, for one that shows it. A consumer
     * given only the {@link ObservedValue} could not render it — the writer that does is this
     * package's, and it needs the module's declarations to tell a newtype from what it wraps — so
     * the text travels beside the value rather than instead of it. {@link StandinEntry} keeps a
     * stated value and its shown text apart for the same reason.
     *
     * <p>Not a record, and for a different reason from {@link NoClauseWasBroken}'s. A record's
     * canonical constructor says that any combination of its components is a value: true of two
     * independent observations, and false the moment one of them is a rendering of another. Written
     * as one, an {@code answered} of seven could be built beside a {@code shownAnswered} of
     * {@code "TodoId(99)"} and the two accessors would say different things about one observation;
     * and the rendering would sit inside {@code equals}, so writing a value differently would make
     * it a different observation. So the constructor is this package's, and the two are written
     * together where the declarations that relate them are in reach.
     *
     * <p>No equality is defined. Two applications are two observations rather than one answered
     * twice — which is what this face says everywhere about asking a row again — so there is nothing
     * for a value equality over them to mean.
     */
    final class Broken implements ContractObservation {

        private final String why;
        private final ObservedValue answered;
        private final String shownAnswered;

        Broken(String why, ObservedValue answered, String shownAnswered) {
            if (why == null || answered == null || shownAnswered == null) {
                throw new IllegalArgumentException("a broken clause said something about a value");
            }
            this.why = why;
            this.answered = answered;
            this.shownAnswered = shownAnswered;
        }

        /** What the clause said when it did not hold, in the words the runtime writes about one. */
        public String why() {
            return why;
        }

        /** What the implementation answered, structural and loader-free. */
        public ObservedValue answered() {
            return answered;
        }

        /** The same, written the way a fixture writes a value. */
        public String shownAnswered() {
            return shownAnswered;
        }

        @Override
        public String shown() {
            return "a clause did not hold: " + why
                    + System.lineSeparator() + "  answered: " + shownAnswered;
        }

        @Override
        public String toString() {
            return getClass().getSimpleName() + "(" + why + ")";
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
        public String shown() {
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
        public String shown() {
            return "nothing was held to the declaration: " + why.said();
        }
    }
}
