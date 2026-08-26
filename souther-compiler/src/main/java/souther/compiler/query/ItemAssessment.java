package souther.compiler.query;

import souther.compiler.partition.Criterion;
import souther.compiler.partition.Generator;
import souther.compiler.partition.NotOwedReason;

import java.util.Collections;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;

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
     * @param attempt    what building a value here came to, or null where nobody asked for one to be
     *                   built. Null is the absence of the evidence and never a state of the point:
     *                   whether a value was composed is a fact about who asked, and it used to be
     *                   carried here as an attempt saying nobody had — a measurement answering a
     *                   question it was not put (issue #1001)
     */
    record Owed(Criterion criterion, Measurement<Coverage> coverage,
                WritabilityProjection projection, Attempt attempt) implements ItemAssessment {

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
         */
        public boolean worthSearching() {
            if (hasRowWitness()) {
                return false;
            }
            return coverage instanceof Measurement.Complete<Coverage> whole
                            && whole.value() instanceof Coverage.NoHit
                    || coverage instanceof Measurement.NotMeasured<Coverage> none
                            && none.why() == Coverage.NotAsked.NO_ROWS;
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

        /** The same point, with what a search of it came to. */
        public Owed settledBy(Attempt searched) {
            if (attempt != null) {
                throw new IllegalStateException(
                        "a point searched twice: " + criterion + " already has " + attempt);
            }
            return new Owed(criterion, coverage, projection, searched);
        }

        /**
         * What has shown that a row can be written here, read off the three things that show it.
         *
         * <p>Derived and never held. The three grounds are answers to three different questions this
         * record already carries, and a set kept beside them would be the same facts written twice —
         * a value with a row at it and no {@code A_ROW_IS_AT_IT} would be a state somebody could
         * build. Read through, that state cannot be spelled.
         *
         * <p>Which is also what makes composing a search safe. A search changes the {@link #attempt}
         * and nothing else, and every ground is monotone in what it reads, so the set this answers
         * can only grow. It used to be a verdict picked from the evidence by a fixed order, where
         * building a value at a point the rules already proved replaced the proof with the witness —
         * true of whether anything was known, and false of what was doing the knowing.
         */
        public WritabilityEvidence writabilityEvidence() {
            return WritabilityEvidence.of(projection, hasRowWitness(),
                    attempt instanceof Attempt.Built);
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
     * <p>A set and not a choice, because the three are not alternatives — a point the rules prove can
     * have a row at it as well, and a value built at it besides. Held as a sum with one case each,
     * the answer was whichever case an order put first, so the strongest claim there was could be the
     * one left out.
     *
     * <p>Empty is the whole of what {@code Unknown} was. Nothing here can say a point is unwritable:
     * a decoder refusing every candidate that was tried says nothing about the ones that were not, so
     * an empty set is the absence of evidence and never evidence of absence. What says a point cannot
     * be written at is the border refusing to owe it at all.
     */
    record WritabilityEvidence(Set<Ground> grounds) {

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
            EnumSet<Ground> held = EnumSet.noneOf(Ground.class);
            held.addAll(grounds);
            grounds = Collections.unmodifiableSet(held);
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
            return new WritabilityEvidence(grounds);
        }

        /** Whether anything at all has shown a row can be written here. False leaves it open, never
         *  closed. */
        public boolean known() {
            return !grounds.isEmpty();
        }

        /** Whether this ground is among them. */
        public boolean has(Ground ground) {
            return grounds.contains(ground);
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
        enum NotAsked implements souther.compiler.observe.NotMeasuredReason {
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
        enum CouldNotAsk implements souther.compiler.observe.FailureReason {
            /** The rows ran without instrumentation, so no row can be shown to have reached the
             *  comparison. Never a reason for an invariant's line. */
            ARMS_UNREADABLE;

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

        /**
         * What the readings of one authored line come to together.
         *
         * <p>One debt is read at every position of every behavior carrying the type, and each of
         * those readings measures it on its own. What the debt came to is not any one of them: a row
         * standing at the line through {@code draft.owner} is evidence about {@code UserId}, and the
         * reading at {@code activities[*]@CallTask.owner} cannot disagree with it (issue #1062).
         *
         * <p><b>Here and nowhere else.</b> A report, a build's refusal, an editor and the generator
         * all ask what became of a debt, and four foldings of the same readings would be four
         * answers about one line — which is the shape this whole change is undoing.
         *
         * <p>The order is the whole of it. A row found settles the line whatever else went unread,
         * so a hit outranks everything. Below that, a reading that could be hiding a row outranks
         * one that ran out and found none, because the second is an answer and the first is the
         * absence of one. And a reading with no rows to look at is neither: it hides nothing, so it
         * cannot take back a miss another reading established, and where every reading is one there
         * was nothing anywhere to look at.
         */
        static Measurement<Coverage> acrossTheReadings(
                java.util.List<Measurement<Coverage>> readings) {
            if (readings.isEmpty()) {
                throw new IllegalArgumentException(
                        "a debt is what its readings came to, and this is none of them");
            }
            WeakeningSet unread = WeakeningSet.none();
            souther.compiler.observe.NotMeasuredReason unasked = null;
            boolean missed = false;
            for (Measurement<Coverage> reading : readings) {
                // Found is found. Said before anything else is looked at, so that no accounting of
                // what went unread can weaken a row somebody wrote.
                if (reading.made().map(Coverage::hit).orElse(false)) {
                    return new Measurement.Complete<>(new Hit());
                }
                switch (reading) {
                    // A reading of this line that did not run out. Whatever it could not read may
                    // be holding the row.
                    case Measurement.Partial<Coverage> in -> unread = unread.union(in.by());
                    case Measurement.FailedToMeasure<Coverage> stopped -> {
                        if (((CouldNotAsk) stopped.why()).mayHideARow()) {
                            unread = unread.union(stopped.by());
                        }
                    }
                    // The three reasons a question was not put are not one answer here. One that
                    // may be hiding a row is kept as itself rather than turned into a weakening:
                    // nothing was read, so there is no reading for a weakening to be about.
                    case Measurement.NotMeasured<Coverage> none -> {
                        if (((NotAsked) none.why()).mayHideARow()) {
                            unasked = none.why();
                        }
                    }
                    // Read to the end and no row is at the point, which is what a miss is.
                    case Measurement.Complete<Coverage> _ -> missed = true;
                }
            }
            if (!unread.isEmpty()) {
                return new Measurement.Partial<>(new NoHit(), unread);
            }
            // Above a miss another reading established, because a reading that looked at nothing
            // leaves the rows it would have looked at unaccounted for. Both of the reasons that
            // reach here are settings of the build rather than facts about one behavior, so this is
            // reached where every reading says it and not where one of them does.
            if (unasked != null) {
                return new Measurement.NotMeasured<>(unasked);
            }
            return missed ? new Measurement.Complete<>(new NoHit())
                    // Every reading had nothing to look at, so neither has the debt.
                    : new Measurement.NotMeasured<>(NotAsked.NO_ROWS);
        }
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
     */
    sealed interface Attempt {

        /**
         * What a search of the region came to, whichever way it came out.
         *
         * <p>The boundary is which side of the search an outcome is on, and it is a type because it
         * was a sentence. A candidate is composed by walking the region, so everything found out
         * afterwards — a row that was accepted, a row that was refused, decoders that could not be
         * reached — is an outcome of a search that ran and carries what it ran over. What was
         * written instead was a comment saying so, and the one outcome that arrived by a different
         * route was filed as a search nobody made and dropped its region on the way.
         */
        sealed interface Searched extends Attempt {

            /** What the way to the point took in and what it could not, which is what says how much
             *  the outcome beside it is worth. */
            souther.compiler.partition.WayToTheBorder way();
        }

        /** A value at the point, built and accepted by the module's own decoders. */
        record Built(Generator.GeneratedRow row,
                     souther.compiler.partition.WayToTheBorder way) implements Searched {}

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
                          souther.compiler.partition.WayToTheBorder way) implements Searched {}

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
         * What the search ran over that the way to the point does not account for.
         *
         * <p>Asked of the attempt because the attempt is what holds both halves: which conditions
         * were left out of the region, and whether this outcome is one they bear on. Answered at a
         * renderer instead, the two halves were a pair of conditions written into a sentence, and
         * the only way to ask what they came to was to compile a model that produced the sentence.
         *
         * <p>Empty where nothing was left out, and empty where the outcome settles the point on its
         * own: a walk of the whole of what the rules leave that reaches no value proves there is
         * nothing to find whether or not the box it walked held rows that never arrive, since an
         * empty box leaves what it contains empty too. Empty for a row that was built, which is a
         * point answered rather than a search to account for, and for a search nobody made.
         */
        default List<souther.compiler.partition.OnTheWay.Declined> unaccountedFor() {
            return switch (this) {
                case Built _, Unavailable _ -> List.of();
                case Unresolved left -> left.why().reason().provesInfeasible()
                        ? List.of() : left.way().declined();
            };
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
