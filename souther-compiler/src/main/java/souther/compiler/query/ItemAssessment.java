package souther.compiler.query;

import souther.compiler.observe.MeasureReason;
import souther.compiler.partition.Criterion;
import souther.compiler.partition.Generator;
import souther.compiler.partition.NotOwedReason;
import souther.compiler.publish.CanonicalSelection;
import souther.compiler.publish.PublicationOrders;

import java.util.Collection;
import java.util.EnumSet;
import java.util.List;
import java.util.Objects;

/**
 * Everything known about one of the four coverage items of a border.
 *
 * <p>Owed or not, and the difference is the shape and not a field. A point nobody is owed a row at
 * has no coverage to report, nothing to say about whether a row could be written there and no search
 * to account for — so it carries none of those, and a state saying the rules refuse this point and a
 * row is at it cannot be built. Held as one record with a reason beside the measurements, that state
 * is one field away at every place that makes one.
 *
 * <p>Where a row is owed, three answers rather than one, because they are about three things and are
 * established by three different means. What the rows showed is read off what this compilation ran.
 * What the rules prove about a value existing there is read off the rules, whether or not anything
 * was ever built. What the search did is what the search did — and it is kept even where it changed
 * neither of the others, because a point the rules already prove is still one a search can fail to
 * produce a row for, and the person who wanted that row is owed the reason.
 */
public sealed interface ItemAssessment {

    /** No row is owed here, and this is what settles it. */
    record NotOwed(NotOwedReason reason) implements ItemAssessment {}

    /**
     * A row is owed, and this is what became of it.
     *
     * @param projection what reading the rules reaching the value this point sits in established
     *                   about a value being there. What the rules say on their own, so it is settled
     *                   without building anything and stays true whatever a search afterwards makes
     *                   of the point
     * @param searches   what building a value here came to, over every search that was made for it,
     *                   and empty where nobody asked for one to be built. Empty is the absence of
     *                   the evidence and never a state of the point: whether a value was composed is
     *                   a fact about who asked, and it used to be carried here as an attempt saying
     *                   nobody had — a measurement answering a question it was not put.
     *
     *                   <p>Several, because one reading of a line can be searched more than once: a
     *                   helper called from two arms is the same line at the same target, and a row
     *                   for it is composed under each caller's own conditions
     */
    record Owed(Criterion criterion, Measurement<Coverage> coverage,
                WritabilityProjection projection, SearchOutcomes searches)
            implements ItemAssessment {

        /**
         * Whether building a value here would tell anybody anything.
         *
         * <p>The measurement's own answer and not the search's. A point a row already sits at needs
         * no candidate, and one whose measurement never happened is not a piece of work to hand to
         * anybody — offered anyway, both put a specific row in front of an author that may already
         * be written.
         *
         * <p>Which is why the two used to be attempts and are not. "A row is already there" and
         * "this was never measured" are things the measurement says, and a search that reported them
         * was repeating what its own input already held.
         *
         * <p><b>Read over the states rather than off a list of the ones that qualify.</b> Every
         * state says here what it means, so a state added to {@link Measurement} arrives as a
         * compile error rather than as a silent {@code false} — which is the difference between a
         * point nobody searched because nothing would come of it and one nobody searched because
         * the list was written before the state existed.
         */
        public boolean worthSearching() {
            if (hasRowWitness()) {
                return false;
            }
            return switch (coverage) {
                // Read to the end and no row at it, or read as far as it got and no row at it: both
                // are points where a candidate tells somebody something.
                case Measurement.Complete<Coverage> it -> it.value() instanceof Coverage.NoHit;
                case Measurement.Partial<Coverage> it -> it.value() instanceof Coverage.NoHit;
                // No rows to look at is a point worth building one for. The other reasons nobody
                // measured are not: a question this compilation was not put is not work to hand to
                // an author.
                case Measurement.NotMeasured<Coverage> it -> it.why() == Coverage.NotAsked.NO_ROWS;
                // Nothing to build against, which the search would find out again.
                case Measurement.FailedToMeasure<Coverage> _ -> false;
            };
        }

        /**
         * Whether a row this compilation observed stands at the point.
         *
         * <p>Not the coverage measurement's answer, and named so it cannot be read as one. A row
         * that was seen at the point is evidence — of the point being writable, of there being
         * nothing left to search for — and evidence is what this collects. {@code false} is the
         * absence of that evidence and is never {@code NoHit}: a measurement nobody made has no row
         * to show and says nothing about whether one is there.
         *
         * <p>Read over the states rather than through {@code made()}, so that the {@code false} the
         * two value-less arms give is written where it can be read as what it is, and so that a
         * state added to {@link Measurement} arrives here as a compile error rather than as a
         * silent {@code false}.
         */
        public boolean hasRowWitness() {
            return switch (coverage) {
                case Measurement.Complete<Coverage> it -> Coverage.hit(it.value());
                case Measurement.Partial<Coverage> it -> Coverage.hit(it.value());
                // No value, so no row was seen here. Not a finding that none is.
                case Measurement.NotMeasured<Coverage> _,
                     Measurement.FailedToMeasure<Coverage> _ -> false;
            };
        }

        /** The same point, with what one more search of it came to. */
        public Owed settledBy(Attempt searched) {
            return new Owed(criterion, coverage, projection,
                    searches.plus(SearchOutcomes.of(searched)));
        }

        /**
         * What has shown that a row can be written here, read off the three things that show it.
         *
         * <p>Derived and never held. The three grounds are answers to three different questions this
         * record already carries, and a set kept beside them would be the same facts written twice —
         * a value with a row at it and no {@code A_ROW_IS_AT_IT} would be a state somebody could
         * build. Read through, that state cannot be spelled.
         *
         * <p>Which is also what makes composing a search safe. A search adds to the
         * {@link #searches} and changes nothing else, and every ground is monotone in what it reads,
         * so the set this answers can only grow. It used to be a verdict picked from the evidence by
         * a fixed order, where building a value at a point the rules already proved replaced the
         * proof with the witness — true of whether anything was known, and false of what was doing
         * the knowing.
         */
        public WritabilityEvidence writabilityEvidence() {
            // The certified arm and not `Built`. What grounds this is a value shown to be at the
            // point, and a row whose read-back never came back has not been shown to be anywhere —
            // counted here, an observation this compiler cut short would be reported as the model
            // admitting a row, which is the same trade as the one it is here to stop, made the
            // other way round. What that row does license is said by `WritabilityKnowledge`.
            return WritabilityEvidence.of(projection, hasRowWitness(), searches.certified());
        }
    }

    /**
     * What reading the rules established about a value being at a point.
     *
     * <p>Three states because the question has been put in three ways. It was a boolean, and the
     * {@code false} stood both for a reading that ran and proved nothing — a rule left unread, a
     * count with no value behind it — and for a line nobody put the question to at all. That is the
     * shape #997 took out of the coverage measurement, one layer down: an answer manufactured for a
     * question nobody asked, told apart from a real answer by nothing.
     *
     * <p>Nothing here says a point cannot be written at. What refuses a point is the border declining
     * to owe a row at it ({@link NotOwed}), which is a different shape and stays that way.
     */
    enum WritabilityProjection {

        /** The rules reaching the value were read in full and leave the point inside what they
         *  admit. The one state that is evidence. */
        PROVEN,

        /** The reading ran and did not get there. A rule it could not read through, or a count whose
         *  values it cannot show exist — the point is where the reading stopped rather than where
         *  the model does. */
        UNPROVEN,

        /** The question was not put. A line between two positions is the one this exists for: what a
         *  row on it takes is a place both positions admit, and reading each of them on its own does
         *  not answer that. Told apart from {@link #UNPROVEN} so that implementing the reading later
         *  moves a line off this state rather than off an answer somebody wrote for it. */
        NOT_COMPUTED;

        /** Whether this is the state that puts a ground in the evidence. The other two are told apart
         *  for what they say about the reading, and neither is evidence of anything. */
        public boolean proves() {
            return this == PROVEN;
        }

        /** The two answers a reading that ran can come to. For a caller holding the reading's own
         *  boolean, so that the third state is never spelled where it cannot arise. */
        public static WritabilityProjection ofReading(boolean proven) {
            return proven ? PROVEN : UNPROVEN;
        }
    }

    /**
     * What has shown that a row can be written at a point: the grounds, and never a verdict.
     *
     * <p>All of them and not a choice, because the three are not alternatives — a point the rules prove can
     * have a row at it as well, and a value built at it besides. Held as a sum with one case each,
     * the answer was whichever case an order put first, so the strongest claim there was could be the
     * one left out.
     *
     * <p>Empty is the whole of what {@code Unknown} was. Nothing here can say a point is unwritable:
     * a decoder refusing every candidate that was tried says nothing about the ones that were not, so
     * holding none is the absence of evidence and never evidence of absence. What says a point cannot
     * be written at is the border refusing to owe it at all.
     *
     * <p>Held in the order they are published in ({@link PublicationOrders#WRITABILITY_GROUNDS}),
     * which is a decision about what a reader is shown and no ranking of the three. A document
     * writes a row per ground, and reading that order off the declaration would put it in the hands
     * of whoever next tidies the constants.
     */
    record WritabilityEvidence(CanonicalSelection<Ground> grounds) {

        /**
         * One thing that shows a row can be written at a point.
         *
         * <p>No order among them, here or anywhere. There is nothing to rank: a set with two grounds
         * in it holds both, and a reader wanting one of them asks for that one. What order a document
         * writes them in is the document's, and is settled where the document is written.
         */
        public enum Ground {

            /** The rules reaching the value prove the point is inside what they admit. The one ground
             *  that is about the model rather than about this run, so it stands whatever a search
             *  afterwards makes of the point. */
            THE_RULES_PROVE_IT,

            /** A row this compilation read stands at the point, which is a value that went through
             *  the decoder. The only ground that costs nothing to find. */
            A_ROW_IS_AT_IT,

            /** A value at the point was built through the module's own decoders. What was built is
             *  the attempt's to hold; this says only that it was. */
            A_VALUE_WAS_BUILT
        }

        public WritabilityEvidence {
            Objects.requireNonNull(grounds, "a point says what has shown a row can be written at it");
        }

        /** Grounds already known to hold, in the order a document says them. Which of them hold is
         *  the question below, and this one does not ask it. */
        public static WritabilityEvidence of(Collection<Ground> grounds) {
            return new WritabilityEvidence(PublicationOrders.WRITABILITY_GROUNDS.keep(grounds));
        }

        /** The grounds that hold, over the three facts that establish them. Where every one of these
         *  comes from: a caller that assembled a set of its own would be deciding what the facts
         *  beside it establish, which is this method's question and not a caller's. */
        public static WritabilityEvidence of(WritabilityProjection projection, boolean rowIsAtIt,
                                             boolean valueWasBuilt) {
            EnumSet<Ground> grounds = EnumSet.noneOf(Ground.class);
            if (projection.proves()) {
                grounds.add(Ground.THE_RULES_PROVE_IT);
            }
            if (rowIsAtIt) {
                grounds.add(Ground.A_ROW_IS_AT_IT);
            }
            if (valueWasBuilt) {
                grounds.add(Ground.A_VALUE_WAS_BUILT);
            }
            return of(grounds);
        }

        /** Whether anything at all has shown a row can be written here. False leaves it open, never
         *  closed. */
        public boolean known() {
            return !grounds.isEmpty();
        }

        /** Whether this ground is among them. */
        public boolean has(Ground ground) {
            return grounds.written().contains(ground);
        }
    }

    /**
     * Whether a row is at this point, and whether that could be told.
     *
     * <p>A point an invariant drew is met by a row whose value is the boundary. One a fork of a body
     * drew is not: the comparison has to have been evaluated as well, because a value can reach the
     * input of a behavior without reaching the guard that cares about it. That is a fact about the
     * rule and holds of all four of the border's points.
     */
    sealed interface Coverage {

        /** A row is at the point, and — where a fork drew the line — went through the comparison.
         * Found is found: a row settles this whatever else went unread. */
        record Hit() implements Coverage {}

        /**
         * No row that could be read is at the point.
         *
         * <p>Named for what was seen and not for what is so. It was {@code Missed}, which meant
         * "every row that bears on this position was read, and none is at the point" — a claim about
         * the reading as well as about the rows, made by the value itself. Beside it sat
         * {@code Undecided} for the case where the reading was not whole, and the two were one
         * question asked twice: what was found, and how far the finding can be trusted.
         *
         * <p>Now the second is the measurement's. {@code Complete(NoHit)} is what {@code Missed}
         * claimed and {@code Partial(NoHit, ...)} is what {@code Undecided} said, and neither the
         * name nor a reader has to carry the difference.
         */
        record NoHit() implements Coverage {}

        /** Why the question was not put. */
        enum NotAsked implements NotMeasuredReason {
            /** The build asked for no measurement at all, so no row was read against any line.
             *  Said by every line whatever drew it, unlike the two below. */
            NOT_ASKED,
            /** The build did not ask for the arms, and a line a fork drew is met by reaching the
             *  comparison rather than by writing the value. Never a reason for an invariant's line,
             *  which needs no arms. */
            ARMS_NOT_ASKED,
            /** No row names this behavior. */
            NO_ROWS;

            /**
             * What each of these is a fact about.
             *
             * <p>Which of them a line says is settled by the level the build asked for and by
             * whether a fork or an invariant drew the line, and the first of those is one value for
             * the whole run. So the two settings say the same thing at every reading of every line
             * they reach, and only the third is something one behavior can say and the next one
             * not.
             *
             * <p><b>Not what {@link #mayHideARow()} answers, and the two are not read off each
             * other.</b> They agree over these three constants and part over {@link CouldNotAsk},
             * which is a fact about the behavior that may well be hiding a row.
             */
            @Override
            public MeasureReason.About about() {
                return switch (this) {
                    case NOT_ASKED, ARMS_NOT_ASKED -> MeasureReason.About.THE_RUN;
                    case NO_ROWS -> MeasureReason.About.THE_BEHAVIOR;
                };
            }

            /**
             * Whether a row at the point could be sitting behind this and not have been seen.
             *
             * <p>Asked of the reason and not of the state around it. Three of these are one
             * {@code NotMeasured} and they do not mean one thing when the answers of several
             * readings are put together: rows the build never looked at may be standing at the
             * point, and rows that do not exist cannot be. Read as the state — "nothing was
             * measured, so nothing is known" — a reading of a behavior nobody wrote a row for
             * would hold open a line another reading had shown a row misses.
             */
            public boolean mayHideARow() {
                return this != NO_ROWS;
            }
        }

        /** Why the question was put and could not be answered. */
        enum CouldNotAsk implements FailureReason {
            /** The rows ran without instrumentation, so no row can be shown to have reached the
             *  comparison. Never a reason for an invariant's line. */
            ARMS_UNREADABLE;

            /** This behavior's rows, which ran and were not recorded. Another behavior of the same
             *  run can have been read to the end, so this is nothing the run says. */
            @Override
            public MeasureReason.About about() {
                return MeasureReason.About.THE_BEHAVIOR;
            }

            /** Whether a row at the point could be sitting behind this, as {@link NotAsked} answers
             *  it. The rows ran, so one of them may have reached the comparison unrecorded. */
            public boolean mayHideARow() {
                return true;
            }
        }

        /**
         * Whether this is a row at the point.
         *
         * <p>Asked of the value and never of the measurement around it. It used to take a
         * {@code Measurement<Coverage>} and answer {@code false} for all three of {@code
         * Complete(NoHit)}, a measurement nobody made and one that could not be finished — so the
         * one answer the rows established and the two states with no answer at all came out as the
         * same boolean, and a document writing it said no row was at a point nothing had looked at
         * (issue #997). What has no value has no answer here, and a caller wanting one for a
         * measurement asks {@link Owed#hasRowWitness()}, which is a different question.
         */
        static boolean hit(Coverage coverage) {
            return coverage instanceof Hit;
        }

        // What the readings of one authored line come to together is
        // ObligationCoverage.acrossTheReadings. It is a different type and not a state of this
        // measure: a reading may be made in part and have found a row, and a debt cannot be.
    }

    /**
     * What was built at this point, and what came of it.
     *
     * <p>Its own answer and not a shade of {@link WritabilityEvidence}. A point the projection already
     * proved is one a search can still fail to reach — the two are about different things, and a
     * reader that recovered the attempt from the grounds would find nothing to say about a row it
     * could not produce at a point it knows exists. The report reads the grounds; {@code --generate}
     * reads this.
     *
     * <p>Made once. The row a person is offered and the value that witnessed the point are the same
     * value, built one time and read twice.
     *
     * <p><b>The outcomes, and the things that may be true of one.</b> The outcomes are what
     * happened and are exclusive, so a reader asking which of them this is asks an exhaustive
     * switch. What may be true of one — that a row came of it, that a search ran, that a figure of
     * this compiler's left the point unestablished — cuts across them: a row that was built and not
     * read back is both a row somebody may have and a point this compiler left open, and neither of
     * those is the other's special case. Written as one hierarchy, one of the three had to be the
     * spine and the others became fields or were read off the spelling of whichever arm a reader
     * had in hand.
     */
    sealed interface Attempt
            permits Attempt.Certified, Attempt.Unverified, Attempt.Stopped, Attempt.Limited,
                    Attempt.Unplanned, Attempt.Unresolved, Attempt.Unavailable {

        /**
         * What a search of the region came to, whichever way it came out.
         *
         * <p>The boundary is which side of the search an outcome is on, and it is a type because it
         * was a sentence. A candidate is composed by walking the region, so everything found out
         * afterwards — a row that was accepted, a row that was refused, decoders that could not be
         * reached — is an outcome of a search that ran and carries what it ran over. What was
         * written instead was a comment saying so, and the one outcome that arrived by a different
         * route was filed as a search nobody made and dropped its region on the way.
         *
         * <p>Beside {@link Attempt} rather than under it. Every outcome but one is a search that
         * ran, and making this the spine of the outcomes would put the one that is not — a search
         * nobody could run — outside a hierarchy it belongs in.
         */
        sealed interface Searched
                permits Certified, Unverified, Stopped, Limited, Unresolved {

            /** What the way to the point took in and what it could not, which is what says how much
             *  the outcome beside it is worth. */
            souther.compiler.partition.WayToTheBorder way();

            /**
             * And what the way did state that no value was composed under.
             *
             * <p>Beside the way rather than on it. What the walk came to is the walk's answer and a
             * condition it stated stays stated; that the composer could not act on one is a fact
             * about a later stage, and written onto the way it would be one condition wearing two
             * of the walk's answers. Both halves are put together where a reader wants one list
             * ({@link #unaccountedFor()}).
             */
            List<souther.compiler.partition.ReachabilityGap.Uncomposed> uncomposed();
        }

        /**
         * A value composed for the point and accepted by the module's own decoders.
         *
         * <p>Composed <em>for</em> it and not established to be at it, which is the whole of what
         * this word promises: {@link Unverified} is the case where nothing placed the value, so a
         * contract saying a value at the point would be false of one of its own arms.
         *
         * <p><b>What was built, and whether it was read back where it was built for, are two
         * things.</b> Composing a value that the decoders take does not say the value lands at the
         * point — a rule the composer could not act on refuses a candidate the composer thought it
         * had placed — so the row is read again after it is built. Which leaves three outcomes and
         * not two: the reading agreed, the reading disagreed, and the reading did not happen.
         *
         * <p>Held as one case, the third can only be said as the second: a value whose read-back a
         * limit cuts short is filed as a search that composed nothing, and the point it stands at
         * is then reported as one nothing can write a row at. Held as a boolean beside the row,
         * every reader decides again what the boolean licenses.
         *
         * <p>So this is what the two share — a row was built, and whoever wants it can have it —
         * and the arms below are what only one of them may say. A reader asking for the row asks
         * for {@link Built}; a reader asking whether anything showed the point writable asks for
         * {@link Certified}, and gets a compile error rather than a silent yes if a third way of
         * being built arrives.
         */
        sealed interface Built permits Certified, Unverified {

            /** The value this search composed, whichever of the two this is. */
            Generator.GeneratedRow row();

            /** A row composed where the whole way was stated and used. */
            static Certified certified(Generator.GeneratedRow row,
                                       souther.compiler.partition.WayToTheBorder way) {
                return new Certified(row, way, List.of());
            }
        }

        /**
         * An attempt whose showing cannot establish the point, because of a figure of this
         * compiler's.
         *
         * <p>Across the outcomes rather than one of them, because what a figure costs depends on
         * how far the attempt had got. Before anything was composed, there is no row and the point
         * is left with nothing; after, there is a row and what is missing is the reading that would
         * have placed it; and a plan short of the value's positions leaves an answer that is about
         * less than the point had. All of them are this compiler's own limit and none of them is
         * anything the model said, which is the one question an account puts to them.
         *
         * <p><b>The one thing they share, and the reason it is said here and not further down.</b>
         * These outcomes have different histories — one search stopped, one ran to the end of a
         * short plan, one never ran at all — and holding them as one outcome would make the history
         * something a reader recovers from a field. What is common is what an account needs and no
         * more: the question is open, and open because of a figure somebody could raise.
         *
         * <p><b>Nothing here says a row cannot be written.</b> What each of these licenses is that
         * the question is open — which is what tells it from a point nothing ever promised.
         */
        sealed interface Prevented permits Unverified, Stopped, Limited, Unplanned {

            /** Which figure of this compiler's the point is open on, in the words the account
             *  reads. */
            EstablishmentGap by();
        }

        /** Built, and read back standing where it was built for. */
        record Certified(Generator.GeneratedRow row,
                         souther.compiler.partition.WayToTheBorder way,
                         List<souther.compiler.partition.ReachabilityGap.Uncomposed> uncomposed)
                implements Attempt, Searched, Built {

            public Certified {
                uncomposed = List.copyOf(uncomposed);
            }
        }

        /**
         * Built, and the reading that would have said where it stands did not come back.
         *
         * <p>Nothing here is about the model. The row is as much a row as {@link Certified}'s and is
         * offered as one; what is missing is this compiler's own confirmation, and {@code why} is
         * what stopped it.
         *
         * <p>An observation and never anything else. What was stopped here is a reading of a value
         * that exists, so the only budget that can be named is one an observation ran out of — a
         * budget that stopped the composing stopped it before there was anything to read, which is
         * {@link Stopped}. Written as any gap at all, the two states a search comes back in could be
         * built holding each other's reasons.
         */
        record Unverified(Generator.GeneratedRow row,
                          souther.compiler.partition.WayToTheBorder way,
                          List<souther.compiler.partition.ReachabilityGap.Uncomposed> uncomposed,
                          EstablishmentGap.Observation why)
                implements Attempt, Searched, Built, Prevented {

            public Unverified {
                uncomposed = List.copyOf(uncomposed);
                Objects.requireNonNull(why, "a row nothing certified says what stopped it");
            }

            @Override
            public EstablishmentGap by() {
                return why;
            }
        }

        /**
         * A budget of this compiler's stopped the search before any value was composed.
         *
         * <p>Told apart from {@link Unresolved} by what it licenses and not by how it feels. A
         * search that ran through what it had and came back with nothing leaves a point nothing has
         * promised anything about; a search this compiler ended leaves a point whose question is
         * open, and open for a reason with a figure attached to it. Held as one, the second was read
         * as the first, and an obligation this compiler declined to work on left the count as one
         * the model admits no row at.
         *
         * <p>Carries the way and what the composer could not act on, like every other outcome of a
         * search: the walk happened, and where it happened is what says how much the rest is worth.
         *
         * <p>{@code why} says what such a search comes back with, which is the word it has always
         * come back with; {@code by} is which budget it was. The first cannot be read back from the
         * second's absence and the second is not recoverable from the first, so both are carried.
         */
        record Stopped(Generator.UnresolvedCombination why,
                       souther.compiler.partition.WayToTheBorder way,
                       List<souther.compiler.partition.ReachabilityGap.Uncomposed> uncomposed,
                       EstablishmentGap.Composition stoppedBy)
                implements Attempt, Searched, Prevented {

            public Stopped {
                uncomposed = List.copyOf(uncomposed);
                Objects.requireNonNull(why, "a search that came to nothing says so in its own word");
                Objects.requireNonNull(stoppedBy, "a search this compiler stopped says which"
                        + " budget stopped it");
                // Carried across the boundary and checked again here, because a copy that travels
                // is a copy that can be made to travel wrong. What the word is remains the budgets'
                // to say at both ends, so neither end holds a pair that disagrees.
                if (why.reason() != Generator.UnresolvedCombination.Reason
                        .wordFor(stoppedBy.budgets().written())) {
                    throw new IllegalArgumentException("a search stopped by "
                            + stoppedBy.budgets() + " does not come back with " + why.reason());
                }
            }

            @Override
            public EstablishmentGap by() {
                return stoppedBy;
            }
        }

        /**
         * The search came to an answer of its own, over less than the point had.
         *
         * <p><b>Beside {@link Stopped} and not a shape of it.</b> A stopped search has no outcome
         * but the stopping, so the word it comes back with follows from the budgets and is checked
         * against them at both ends. Here the search ran to the end of what it was handed and said
         * what it found; the figure says the thing it was handed was short of the point. Neither
         * half follows from the other, so no rule relates them and none may be written — a figure
         * that stops no search has no word for a reader to check against.
         *
         * <p>What it licenses is what {@link Stopped} licenses and nothing more: the question is
         * open, and open for a figure somebody could raise. What it refuses is the reading that the
         * word is the whole story — which is how a point this compiler declined to plan for came to
         * be counted as one the model admits no row at.
         */
        record Limited(Generator.UnresolvedCombination why,
                       souther.compiler.partition.WayToTheBorder way,
                       List<souther.compiler.partition.ReachabilityGap.Uncomposed> uncomposed,
                       EstablishmentGap.Composition limitedBy)
                implements Attempt, Searched, Prevented {

            public Limited {
                uncomposed = List.copyOf(uncomposed);
                Objects.requireNonNull(why, "a search that came to nothing says so in its own word");
                Objects.requireNonNull(limitedBy, "an answer short of what the point had says which"
                        + " figure made it short");
            }

            @Override
            public EstablishmentGap by() {
                return limitedBy;
            }
        }

        /**
         * No search ran: what the point asks for is under a position this compiler declined to
         * plan.
         *
         * <p><b>Not {@link Searched}, which is the whole of why it is its own arm.</b> The value
         * was never planned, so nothing walked the region and nothing came back from it — and an
         * outcome that said a search ran would put a reading nobody looked at among the ones that
         * were looked at. {@link Limited} is the other side of that: there the search did run, over
         * a plan short of the point, and its own word is worth carrying.
         *
         * <p>Its word says no search happened rather than what one found. Given a search's word,
         * the two arms would be told apart only by which one a reader happened to be holding, and
         * the history would be something recovered from a field.
         *
         * <p>{@link Prevented} all the same, because the account's question is the same for both:
         * the point is open, and open on a figure somebody could raise.
         *
         * <p>Carries the way to the point, which was walked before any of this: how the point was
         * reached is what says what the rest is worth, and a condition the walk had no words for is
         * still owed to a reader.
         */
        record Unplanned(Generator.UnresolvedCombination why,
                         souther.compiler.partition.WayToTheBorder way,
                         List<souther.compiler.partition.ReachabilityGap.Uncomposed> uncomposed,
                         EstablishmentGap.Composition limitedBy)
                implements Attempt, Prevented {

            public Unplanned {
                uncomposed = List.copyOf(uncomposed);
                Objects.requireNonNull(why, "an attempt says what it came to in its own word");
                Objects.requireNonNull(limitedBy, "a point nothing could be planned for says which"
                        + " figure left it unplanned");
            }

            @Override
            public EstablishmentGap by() {
                return limitedBy;
            }
        }

        /**
         * The search ran and no row came of it.
         *
         * <p>Named for what happened and not for one of the ways it happens. Every candidate being
         * refused is one of them; a point with no value to write at all, and a search that stopped
         * before it got here, are the others, and only the first is the decoder saying anything. A
         * name that said "refused" would invite a reader to take the other two for a decision the
         * decoder made — which is the mistake this type exists to prevent, one size down.
         *
         * <p>How the point came to be searched where it was is the half of the answer that says how
         * much the other half is worth, so it carries the way like every other outcome of a search.
         */
        record Unresolved(Generator.UnresolvedCombination why,
                          souther.compiler.partition.WayToTheBorder way,
                          List<souther.compiler.partition.ReachabilityGap.Uncomposed> uncomposed)
                implements Attempt, Searched {

            public Unresolved {
                uncomposed = List.copyOf(uncomposed);
            }

            /** A search that came to nothing where the whole way was stated and used. */
            public Unresolved(Generator.UnresolvedCombination why,
                              souther.compiler.partition.WayToTheBorder way) {
                this(why, way, List.of());
            }
        }

        /**
         * A search was asked for and there was nothing to run it against.
         *
         * <p>Separate from a refusal because they license different sentences: one is a fact about
         * values, the other is a fact about this run.
         *
         * <p>What is not here is anybody not having asked. "A row is already there" and "this was
         * never measured" were reasons and are the measurement's own answers ({@link
         * Owed#worthSearching}); "the build composed no values" was a reason and is now the absence
         * of an attempt, because a search reporting that nobody asked for it is a search that ran.
         */
        record Unavailable(Reason reason) implements Attempt {}

        enum Reason {
            /** The module's classes were not there to build against. */
            NO_CLASSES
            // The decoders being out of reach was one of these and is not. It is found by running a
            // candidate, and a candidate is something a search of the region already produced — so
            // it is a search that came to nothing, which is `Unresolved`, and it says so in the
            // generator's own words. Left here, it was the one search whose region went unrecorded.
        }

        /**
         * Every condition on the way that the row this came to was not composed against, and which
         * stage let each one go.
         *
         * <p>Asked of the attempt because the attempt is what holds both halves: which conditions
         * were left out, and whether this outcome is one they bear on. Answered at a renderer
         * instead, the two halves were a pair of conditions written into a sentence, and the only
         * way to ask what they came to was to compile a model that produced the sentence.
         *
         * <p>Put together here and kept apart everywhere else. A condition the walk had no words
         * for and one it stated that nothing could compose a value under leave the same gap for a
         * reader and are different facts to act on, so what comes back is one list of two shapes
         * rather than one shape that has lost which of them it was.
         *
         * <p>Empty where nothing was left out, and empty where the outcome settles the point on its
         * own: a walk of the whole of what the rules leave that reaches no value proves there is
         * nothing to find whether or not the box it walked held rows that never arrive, since an
         * empty box leaves what it contains empty too. Empty for a row that was built, which is a
         * point answered rather than a search to account for, and for a search nobody made.
         */
        default List<souther.compiler.partition.ReachabilityGap> unaccountedFor() {
            souther.compiler.partition.WayToTheBorder way;
            List<souther.compiler.partition.ReachabilityGap.Uncomposed> uncomposed;
            switch (this) {
                case Unresolved it -> {
                    if (it.why().reason().provesInfeasible()) {
                        return List.of();
                    }
                    way = it.way();
                    uncomposed = it.uncomposed();
                }
                // A search a budget ended walked as far as it walked, and what it could not compose
                // against on the way is the first thing that would explain what it came back with.
                case Stopped it -> {
                    way = it.way();
                    uncomposed = it.uncomposed();
                }
                // And one whose answer was about less than the point had. Its word may be a word
                // that proves nothing is there, and here it does not: what the word is about is
                // what the search was handed, which was short of the point — so the conditions it
                // could not compose against are still owed to a reader.
                case Limited it -> {
                    way = it.way();
                    uncomposed = it.uncomposed();
                }
                // And one no search was run for. The way to the point was walked all the same, and
                // what it had no words for is the first thing that would explain the point being
                // where it is.
                case Unplanned it -> {
                    way = it.way();
                    uncomposed = it.uncomposed();
                }
                case Certified _, Unverified _, Unavailable _ -> {
                    return List.of();
                }
            }
            List<souther.compiler.partition.ReachabilityGap> out = new java.util.ArrayList<>();
            // The walk's, said as the stage it happened at. A condition it had no words for is one
            // nothing downstream ever saw.
            way.declined().forEach(each ->
                    out.add(new souther.compiler.partition.ReachabilityGap.Unstated(each)));
            out.addAll(uncomposed);
            return List.copyOf(out);
        }
    }

    /** This point's own measurement of whether a row is at it, or a settled nothing where no row is
     *  owed here at all. */
    default Measurement<Coverage> weakeningSource() {
        return this instanceof Owed owed ? owed.coverage()
                : new Measurement.Complete<>(new Coverage.NoHit());
    }

    /**
     * How far the coverage half got, as the one word every measure is totalled under.
     *
     * <p>Derived rather than stored. A report adding up what it could and could not measure asks this
     * of each measure in turn, and a copy of the answer kept beside the answer is a second thing to
     * keep in step.
     *
     * <p>A point nobody is owed a row at is complete: the question was put to the model and the model
     * answered it. Read as unmeasured, every bound in a corpus would hold its behavior open for a
     * measurement nobody was ever going to make.
     */
    default WeakeningSet weakening() {
        return switch (this) {
            // A point nobody is owed a row at went without nothing: the question was put to the
            // model and the model answered it. Counted as unmeasured, every bound in a corpus would
            // hold its behavior open for a measurement nobody was ever going to make.
            case NotOwed _ -> WeakeningSet.none();
            case Owed owed -> owed.coverage().weakening();
        };
    }

    /** Whether a row is owed here at all, and so whether the three answers beside it exist. */
    default boolean owed() {
        return this instanceof Owed;
    }

    /**
     * Whether this is a row an author is owed: the point was measured and missed, and something has
     * shown a row can be written there.
     *
     * <p>The two halves are asked of the two answers rather than of one flattened state. A missed
     * point nothing promises is writable is not a gap — the point is where the reading stopped rather
     * than where the model does — and a point nobody measured is not one either. Neither is one
     * missed by rows some of which could not be read: that is a measurement made in part, and what
     * it did not find is undecided rather than absent.
     */
    default boolean isUnmetGap() {
        return this instanceof Owed owed
                && owed.coverage() instanceof Measurement.Complete<Coverage> whole
                && whole.value() instanceof Coverage.NoHit
                && owed.writabilityEvidence().known();
    }
}
