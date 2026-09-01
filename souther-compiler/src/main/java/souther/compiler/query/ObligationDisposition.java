package souther.compiler.query;

import souther.compiler.partition.ReadingGap;

import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * Where one obligation stands in the account a report counts it in.
 *
 * <p>Derived from the evidence and never held beside it. What the readings came to
 * ({@link ObligationCoverage}) and what has shown a row can be written here
 * ({@link ItemAssessment.WritabilityEvidence}) are answers to two questions, and this is the one
 * question a count, a finding and a build's refusal all put: is this row written, owed, or neither.
 * Asked of the evidence at each of those places instead, the three had three chances to read one
 * pair of answers differently.
 *
 * <p>Four states, and three of them are counted. A counted obligation is one the model owes a row at
 * and the rows were read against, so the three make a partition of the denominator: a row stands at
 * it, no row does and the model says one can be written, or nobody can say which. What is not
 * counted is said with every reason it is not, because the reasons are independent — nothing was
 * read <em>and</em> nothing has shown a row can be written is a state, and a disposition naming one
 * of the two would be choosing between them.
 */
public sealed interface ObligationDisposition {

    /** One this account counts, which is one the rows were read against and a row could answer. */
    sealed interface Counted extends ObligationDisposition {}

    /** A row this compilation observed stands at the point. */
    record Met() implements Counted {}

    /**
     * No row is at the point, the readings ran to the end, and something has shown a row can be
     * written there. The one state a finding is made of and a build can be told to refuse over.
     */
    record Unmet() implements Counted {}

    /**
     * No row was seen, and something this compiler could not do is why nobody can say more.
     *
     * <p>Counted and never a finding. Whether a row is at the point is what nobody can say, so an
     * author told to write one may be told to write one they have written; and left out of the
     * count, an obligation the rows may already answer would go unsaid.
     *
     * <p><b>Two questions can be the one nobody can answer, and they are told apart.</b> A reading
     * that could have been holding a row did not run to the end; or the rows were read to the end
     * and it was the showing that a row can be written here that was stopped. Both leave the point
     * undecided and they leave different work: the first is answered by reading more of what is
     * written, the second by this compiler being able to keep more of what it builds. Held as one
     * state, a reader is told a verdict and left to work out which question it is about — from the
     * verdict, which is the one thing that does not say.
     *
     * <p>Both, because one obligation can be both, and either one alone would be a choice of which
     * to tell. At most one of each, and in the order below: what a reader is shown cannot come out
     * of the order a fold happened to put them in.
     */
    record Undecided(List<Uncertainty> because) implements Counted {

        public Undecided {
            if (because == null || because.isEmpty()) {
                throw new IllegalArgumentException(
                        "an obligation nobody can decide says which question is open");
            }
            because = List.copyOf(because);
            for (int i = 1; i < because.size(); i++) {
                if (orderOf(because.get(i - 1)) >= orderOf(because.get(i))) {
                    throw new IllegalArgumentException(
                            "the open questions are said once each and in order: " + because);
                }
            }
        }
    }

    /**
     * Which question about an obligation is the one nothing answered, and what it is open on.
     *
     * <p>The answer travels with the question. A name for the question alone sends every reader
     * back to the evidence beside it to work out what to say, and each of them works it out on its
     * own terms — so what one point is open on is as many answers as there are readers, and which
     * of them a document says comes out of which reader wrote that line.
     */
    sealed interface Uncertainty {

        /**
         * Whether a row that is written stands at the point: a reading of the rows stopped short.
         *
         * <p>With what the readings met, each reason once ({@link ReadingReasons}). Which reading
         * met which is no part of this: the readings are named under the point, one to a line, and
         * an answer that paired them would be answering about a reading in the sentence about the
         * line.
         */
        record WhetherARowIsThere(ReadingReasons met) implements Uncertainty {

            public WhetherARowIsThere {
                Objects.requireNonNull(met, "a reading that stopped short says what it met");
            }
        }

        /**
         * Whether a row can be written at the point: the showing of it stopped short, and this is
         * what stopped it.
         */
        record WhetherARowCanBeWritten(WritabilityKnowledge.Prevented stopped)
                implements Uncertainty {

            public WhetherARowCanBeWritten {
                Objects.requireNonNull(stopped, "a showing that was stopped says what stopped it");
            }
        }
    }

    /**
     * What the readings of a point met, out of what the measurement of it went without.
     *
     * <p>The one crossing from an accounting of facts to what a reader is told. What weakened the
     * measurement is keyed on the border each reading was made at, because a module counting what
     * it could not read counts one fact per line; this point's own explanation is not, because the
     * readings are named under it and a clause said once per reading counts the paths a fact
     * arrived by.
     *
     * <p>Exhaustive, with no {@code default}. A way of weakening a measurement added is a compile
     * error here rather than one that silently says nothing about a point it leaves open — the
     * arms that contribute nothing say so because their reason is written where it happened, and a
     * new arm has to be put on one side or the other before it can be built.
     */
    private static ReadingReasons whatTheReadingsMet(WeakeningSet by) {
        List<ReadingGap> met = new ArrayList<>();
        for (Weakening each : by.causes()) {
            switch (each) {
                // The reading's own reason, and the only one this sentence carries.
                case Weakening.BorderValueUnreadable it -> met.add(it.why());
                // Said where it happened. A row that never ran, a body nothing elaborated and a
                // boundary nothing derived bear on every line at once, so a sentence about one
                // point that repeated them would say of this line what is true of all of them.
                case Weakening.ObservationIncomplete _,
                     Weakening.OutputCasesUnreadable _,
                     Weakening.InputCasesUnreadable _,
                     Weakening.ModelReadingIncomplete _,
                     Weakening.BodiesNotElaborated _,
                     Weakening.BoundaryNotDerived _,
                     Weakening.PairSpaceTruncated _,
                     Weakening.ProofContradicted _,
                     Weakening.ArmsUnsettled _ -> { }
            }
        }
        return ReadingReasons.of(met);
    }

    /**
     * Where one open question sits in the order they are said in.
     *
     * <p>Exhaustive, so a question added is a compile error here rather than one that arrives
     * wherever a fold put it. What a reader does about the two differs — the first is answered by
     * reading more of what is written and the second is not work an author can do — and the first
     * is said first because it is the one they can act on.
     */
    private static int orderOf(Uncertainty question) {
        return switch (question) {
            case Uncertainty.WhetherARowIsThere _ -> 0;
            case Uncertainty.WhetherARowCanBeWritten _ -> 1;
        };
    }

    /** One this account does not count, with every reason it does not. */
    record NotCounted(Set<Reason> because) implements ObligationDisposition {

        public NotCounted {
            if (because == null || because.isEmpty()) {
                throw new IllegalArgumentException(
                        "an obligation left out of the count says why it is out");
            }
            because = Collections.unmodifiableSet(EnumSet.copyOf(because));
        }
    }

    /** Why an obligation is not counted. Both can hold of one obligation. */
    enum Reason {
        /** Nothing was read against the point, so there is nothing to have found. */
        NOTHING_WAS_READ,
        /** Nothing has shown a row can be written here, so a miss is where the reading stopped
         *  rather than where the model does. */
        NOT_KNOWN_TO_BE_WRITABLE
    }

    /**
     * Where {@code coverage} and {@code knowledge} put the obligation.
     *
     * <p>The one place the pair is read, and read coverage first. What the rows came to is what
     * decides which question is even open: a row found is met whatever else is so, a reading that
     * stopped leaves the point undecided whatever anybody built, and a point nothing was read
     * against is out of the count however well the rules prove a value could stand there.
     *
     * <p><b>What has shown a row can be written is a refinement of one of those and not a gate over
     * all of them.</b> It is what tells a miss the rows ran out on from a finding — an author told
     * to write a row at a point nothing promises may be told to write one that cannot exist. Asked
     * before the coverage instead, it takes an obligation nobody could decide out of the count as
     * well, and the account then says the model admits no row at a point where the rows simply went
     * unread.
     *
     * <p>And the middle answer of the three is why that refinement has three arms rather than two.
     * A point where the showing was stopped by a budget of this compiler's is not one where nothing
     * promises a row: it is one where the promise was being made and did not arrive. Counted, and
     * never a finding.
     */
    static ObligationDisposition of(ObligationCoverage coverage, WritabilityKnowledge knowledge) {
        return switch (coverage) {
            case ObligationCoverage.Witnessed _ -> new Met();
            // What the rows left open, and beside it whatever else is open about the same point. A
            // reading that stopped and a showing that was stopped are two questions, and a point
            // where both happened is undecided about both.
            case ObligationCoverage.Undecided it -> {
                List<Uncertainty> open = new ArrayList<>();
                open.add(new Uncertainty.WhetherARowIsThere(whatTheReadingsMet(it.by())));
                if (knowledge instanceof WritabilityKnowledge.Prevented stopped) {
                    open.add(new Uncertainty.WhetherARowCanBeWritten(stopped));
                }
                yield new Undecided(open);
            }
            case ObligationCoverage.Missed _ -> switch (knowledge) {
                case WritabilityKnowledge.Established _ -> new Unmet();
                // The rows are read out and no row is at the point, and what would have shown a row
                // can be written was stopped on the way. The obligation stays in the count — a
                // budget of this compiler's is not the model refusing anything — and no finding is
                // made of it, because nothing here can say the row an author would write is one
                // that exists.
                case WritabilityKnowledge.Prevented stopped -> new Undecided(
                        List.of(new Uncertainty.WhetherARowCanBeWritten(stopped)));
                case WritabilityKnowledge.NoEvidence _ ->
                        new NotCounted(EnumSet.of(Reason.NOT_KNOWN_TO_BE_WRITABLE));
            };
            // Nothing was read against it, so there is nothing to have found. What is known about a
            // row being writable there is said beside that rather than instead of it: the two are
            // independent facts about the point and a reader is owed both.
            case ObligationCoverage.NotMeasured _ -> {
                Set<Reason> because = EnumSet.of(Reason.NOTHING_WAS_READ);
                if (!(knowledge instanceof WritabilityKnowledge.Established)) {
                    because.add(Reason.NOT_KNOWN_TO_BE_WRITABLE);
                }
                yield new NotCounted(because);
            }
        };
    }
}
