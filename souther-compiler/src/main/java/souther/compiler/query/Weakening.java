package souther.compiler.query;

import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.observe.Figure;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.RowRef;
import souther.compiler.observe.RunSensitivity;
import souther.compiler.partition.CasesTheRowsTook;
import souther.compiler.partition.ClosureGap;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.DecisionRule;
import souther.compiler.partition.DerivedValue;
import souther.compiler.partition.Replacement;
import souther.compiler.types.SourceConstructOrigin;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * One thing that leaves a measurement weaker than it looks.
 *
 * <p>What a measure kept as a local variable and threw away. Every measure that came back
 * {@code PARTIAL} worked out a boolean, and every reader above it worked the same boolean out again
 * from the fields beside the answer — a flag on the combinations, the rules nothing took in, the
 * rows that could not be classified. Each of those was a second representation of one assertion, and
 * each was that measure's own business to know about (issue #953).
 *
 * <p><b>A sum and not a shared shape.</b> Every arm holds what the reader that found it produced,
 * whole. Written as one record with a code and a subject wide enough to hold a rule, an axis, a
 * probe and a source, every reader wanting the fact would take the subject apart again by the code
 * beside it — which is the reconstruction this type exists to stop, one level down.
 *
 * <p>So what the arms share is that they weaken a measurement and travel up to whoever assembles
 * one. That is the only operation anything performs on them, and it is the only thing worth having
 * in common: {@link WeakeningSet#union}.
 *
 * <p><b>Every arm is identified well enough to survive that union.</b> Two facts that are one fact
 * collapse — one rule this compiler could not read, found from three behaviors, is one thing to tell
 * an author — and two that are not must not. A bare probe number is not a fact, which is why the
 * arms that are about one behavior say which.
 *
 * <p><b>What a set of these is.</b> Not every true thing that follows from a measurement being
 * weaker than it looks: the causes a reader is to be told about, each said once. A stop this
 * compiler made has consequences that are true sentences about the model — a position nothing could
 * be read into is a position whose rules nothing read — and a reader given both has to work out that
 * the second follows from the first (issue #1084).
 *
 * <p>So one of two findings is left out exactly where a provenance says it is derived from the
 * other, and never because the two arrive with the same path on them. A path is where something is
 * and not what caused it: at one position a reading can enter and lose a clause of its own while a
 * rule about the value from outside goes unanswered, and those are two causes an author acts on
 * separately. Which findings stand in that relation is written down where the arms are
 * ({@link souther.compiler.partition.MeasureClosure}), so a fold is a case of a {@code switch} with
 * no {@code default} rather than a rule anybody applies by eye.
 */
public sealed interface Weakening {

    /**
     * Whether a run of this compiler that allows more could come to a different answer about this.
     *
     * <p>What a wider run is, is written where the answer is
     * ({@link RunSensitivity}). What matters here is which arms decide and
     * which pass the question on: an arm that holds what stopped it asks that, and only an arm that
     * <em>is</em> the first place the fact exists answers for itself. Written the other way round —
     * a switch over the arms with an answer per arm — this would be the reconstruction the type
     * exists to stop, one level up: an observation's code already knows, and a second reading of it
     * here is a second thing to keep in step.
     *
     * <p>So three ask — {@link ObservationIncomplete} asks its code, {@link BorderValueUnreadable}
     * asks its reading, {@link ModelReadingIncomplete} asks its gap — and the other eight answer,
     * because for those there is nothing further in to ask.
     */
    RunSensitivity runSensitivity();

    /**
     * Every figure of this compiler's that stopped it, each as it stood where the comparison was
     * made, whatever else stopped it beside them: a weakening a wider run leaves standing may have
     * reached a figure on the way, and a reader is told it did.
     *
     * <p>Carried and never worked out here. Each arm hands over what the place that stopped put in
     * it, and an arm that holds what stopped it asks that, as {@link #runSensitivity} does: a
     * figure named from the word an arm is published as would name one of the figures that share
     * the word, and a reader raising it may be raising the one that stopped nothing.
     *
     * <p>Not every {@link RunSensitivity#MAY_CHANGE} has one. A border left out because nothing
     * watched the runs ({@link ABorderNotHeldAgainstTheLinesBesideIt.Why#NOTHING_WATCHED_THE_RUNS})
     * was stopped by what this build was asked to record, which is a way of running and not a
     * figure, and so is a weight left undecided by the same
     * ({@link AWeightNotDecided.Why#A_RUN_WAS_NOT_WATCHED}). They are the two: every other stop a
     * wider run may get past was compared against a figure, and carries it.
     */
    default List<Figure> figures() {
        return switch (this) {
            case ObservationIncomplete it -> it.met().figures();
            case OutputCasesUnreadable _, InputCasesUnreadable _,
                 ItemsPlaceNotWorkedOut _, AReadingNotTiedToItsLine _, AWeightNotDecided _,
                 ABorderNotHeldAgainstTheLinesBesideIt _,
                 BodyNotInEvaluation _, BoundaryNotDerived _, InputNotRead _,
                 ProofContradicted _, ProofOfAWayContradicted _, ArmsUnsettled _,
                 DecisionOfRowUnreadable _, DecisionRunNotWatched _, DecisionRuleReadShort _,
                 KeyedOverwriteCasesUnmeasured _, ReachableNodeCasesUnmeasured _,
                 MeetingsNotPlaced _, MeetingsNotJoined _ -> List.of();
            case BorderValueUnreadable it -> it.why().figures();
            case BorderReadingsNotExhausted it -> it.limits();
            case ModelReadingIncomplete it -> it.cause().figures();
            case PairSpaceTruncated it -> it.limits();
            case MeetingsNotWalked it -> it.limits();
            case DecisionReadingIncomplete it -> switch (it.why()) {
                case DecisionReading.Enumeration.Complete _ -> List.of();
                case DecisionReading.Enumeration.StoppedAtAFigure(CompositionBudget figure) ->
                        List.of(figure.figure());
            };
            case RewriteUndecided it -> it.why().figures();
        };
    }

    /**
     * Something the rows were to be measured from was not observed.
     *
     * <p>The vocabulary already existed and was already collected, a list at a time, beside the
     * measures rather than inside them — which is why the report had to join the two by hand and
     * why a behavior's status was decided from a list its measures never saw.
     */
    record ObservationIncomplete(Incompleteness.Met met) implements Weakening {

        public ObservationIncomplete {
            if (met == null) {
                throw new IllegalArgumentException("something went unobserved, and this is what");
            }
        }

        /**
         * One occurrence of it, as the reader that met it produced one.
         *
         * <p>Where it was met is evidence and not the fact — a module's classes failing to be
         * instrumented is one fact however many sources went looking for them — so it arrives as a
         * place this may be cited at and never as part of what tells two of these apart.
         */
        public static ObservationIncomplete of(Incompleteness occurrence) {
            return new ObservationIncomplete(Incompleteness.Met.of(occurrence));
        }

        /** The code's own answer, which is the code's to give because every producer of one agrees
         *  about it. */
        @Override
        public RunSensitivity runSensitivity() {
            return met.fact().code().runSensitivity();
        }
    }

    /**
     * Rows that state an expectation whose case could not be read
     * ({@link RowOutcome.ExpectedCase.Unread}) while a case of the output is expected by no row, so
     * that case is undecided rather than missing. A row whose answer is owed is not one of them: it
     * expects nothing, and no case waits on it.
     *
     * <p>Where every case is expected by some row there is nothing for these rows to decide, and
     * this is not met.
     *
     * @param unread which rows, so that a reader is sent to the ones to write the case out in. A
     *               set, in the order the rows were read: which rows they are is the fact, and two
     *               of these holding the same rows are one fact however they were gathered
     */
    record OutputCasesUnreadable(String behavior, Set<RowRef> unread) implements Weakening {

        public OutputCasesUnreadable {
            unread = Collections.unmodifiableSet(new LinkedHashSet<>(unread));
            if (unread.isEmpty()) {
                throw new IllegalArgumentException("no row of `" + behavior
                        + "` went unread, so no case of it waits on one");
            }
        }

        /** Whether a row's text names a case is the same however much a run allows. A row a
         *  figure stopped before its expectation was read is stopped in the reading of the rows
         *  as well, and that gap carries the figure. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    /**
     * The same at one of a behavior's inputs, counted from zero: rows whose input case could not be
     * read, where a set they would be in lacks a case a row can be written at.
     *
     * @param unread which rows, those whose case could change one of those sets, as a set in the
     *               order they were read. A row whose sets are already full is not among them:
     *               reading it would change nothing
     */
    record InputCasesUnreadable(String behavior, int at, Set<RowRef> unread)
            implements Weakening {

        public InputCasesUnreadable {
            unread = Collections.unmodifiableSet(new LinkedHashSet<>(unread));
            if (unread.isEmpty()) {
                throw new IllegalArgumentException("no row of `" + behavior
                        + "` went unread at input #" + (at + 1) + ", so no case there waits on one");
            }
        }

        /** The same, for the same reason. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    /**
     * A row's value at one border could not be read, so what is not found at that border is
     * undecided rather than absent.
     *
     * <p>With what stopped the reading, one of these per reason, so that a border stopped in two
     * ways says both — which a set does for free, and a record holding the reasons would leave to
     * whoever wrote the sentence. The reasons are the reading's own ({@link
     * souther.compiler.partition.ReadingGap}) and are carried rather than folded: a value a limit
     * shortened, a value nothing could decode and a place the walk never reached leave the same
     * hole and are three different pieces of news.
     */
    record BorderValueUnreadable(souther.compiler.partition.Border border,
                                 souther.compiler.partition.ReadingGap why)
            implements Weakening {

        /** The reading's own answer, which is the whole of why the reason travels rather than being
         *  folded here. */
        @Override
        public RunSensitivity runSensitivity() {
            return why.runSensitivity();
        }
    }

    /**
     * The rows neither fix nor leave unfixed how one position weighs into a value derived from
     * several positions, for a reason that exists first in the weights.
     *
     * <p>None of the reasons is a claim about the rows, so the weight is no finding, and none of
     * them is a weight fixed either: a verdict that rested on it would rest on nothing.
     *
     * <p>Only what is first a fact of the weights is said here. A border whose rows were read in
     * part, or stopped at a figure, already says so in its own words, with its own answer about a
     * wider run, and the undecided weight carries those as they are rather than answering for them
     * a second time. What is left for this is the weights' own: nothing of the computation was read,
     * a border was left short with no word of its own, a run nothing watched, and the exact
     * arithmetic giving out on a changed weight.
     *
     * <p>Owned by the weights and not by a border. The computation is one however many borders cut
     * it, and the borders of a computation cut at several places are not asked for the lines beside
     * them.
     */
    record AWeightNotDecided(String behavior, DerivedValue value, NumericTerm position, Why why)
            implements Weakening {

        /** Why the weight is neither fixed nor shown unfixed. */
        public enum Why {
            /** No border of the computation was read against the rows. */
            NO_BORDER_OF_IT_WAS_READ(RunSensitivity.UNAFFECTED),
            /** A border was read short and nothing else says how: its rows are not all read. */
            A_BORDER_WAS_NOT_READ_IN_FULL(RunSensitivity.UNAFFECTED),
            /** A row was left out because nothing watched its run. What watched it is what this
             *  build asked to record, so a build that records more reads the row. */
            A_RUN_WAS_NOT_WATCHED(RunSensitivity.MAY_CHANGE),
            /** A model's own decimals put a changed weight, or a row under it, out of the exact
             *  arithmetic's reach. No allowance stopped the working out. */
            THE_ARITHMETIC_GAVE_OUT(RunSensitivity.UNAFFECTED);

            private final RunSensitivity sensitivity;

            Why(RunSensitivity sensitivity) {
                this.sensitivity = sensitivity;
            }

            RunSensitivity sensitivity() {
                return sensitivity;
            }
        }

        public AWeightNotDecided {
            Objects.requireNonNull(behavior, "a weight not decided is a behavior's");
            Objects.requireNonNull(value, "a weight is a weight in some computation");
            Objects.requireNonNull(position, "a weight is the weight of some position");
            Objects.requireNonNull(why, "a weight not decided says why");
        }

        /** Asked of the reason: the ways to be undecided do not answer alike. */
        @Override
        public RunSensitivity runSensitivity() {
            return why.sensitivity();
        }
    }

    /**
     * A reading of a comparison a body wrote that this compiler could not tie to the line its author
     * drew: the comparison turns at the reading's line, and the turn is where a caller's choice turns
     * rather than anywhere shown to be the author's line.
     *
     * <p>A helper's {@code x <= 10} handed {@code if a > 0 then 10 else 11} turns at {@code a = 0},
     * where {@code x} is eleven. Rows at such a line are evidence about the comparison that this
     * reading cannot count for or against a point of the author's line, so what they came to for that
     * point is undecided rather than settled either way.
     */
    record AReadingNotTiedToItsLine(souther.compiler.partition.Border border) implements Weakening {

        public AReadingNotTiedToItsLine {
            if (border == null) {
                throw new IllegalArgumentException("a reading not tied to its line is some line's");
            }
        }

        /** Unaffected either way: what would tie it is a reading this compiler does not make, and
         *  no allowance of a run reaches it. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    /**
     * A coverage item's own place on the order — whether a row is owed there at all — is one a
     * model's own decimals put far enough apart in scale that the exact arithmetic could not read,
     * so what became of it is undecided rather than settled either way.
     *
     * <p>Apart from {@link BorderValueUnreadable}: there a row's value could not be read against a
     * line already known to ask for one; here whether the line asks for a row here at all — is it
     * at the threshold, does the order name a neighbour, does the model leave a run beside it — is
     * what the arithmetic gave out on. Neither a row this compiler could not measure nor a fact the
     * model settled, so counting it as excluded or counting it against coverage would both say more
     * than this found out.
     */
    record ItemsPlaceNotWorkedOut(souther.compiler.partition.Border border,
                                  souther.compiler.numeric.UnheldNumber why) implements Weakening {

        public ItemsPlaceNotWorkedOut {
            if (why == null) {
                throw new IllegalArgumentException("not worked out, in one of the two ways it is not");
            }
        }

        /** Unaffected either way: no allowance of this compiler's stopped the working out, and the
         *  room that ran out, where it was room, is the host's. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    /**
     * A row holds more readings at one border than a point is tried against, so what no reading
     * stands at is undecided rather than absent.
     *
     * <p>Beside {@link BorderValueUnreadable}, and not one of it. There the reading was made and
     * came to nothing; here the readings that were made were read in full and the rest were never
     * made. A row whose positions run inside sequences has one reading per element chosen at each
     * step, and which of them holds the value at the line is the row's business — so a walk that
     * stops part-way through them may say it found the value and may not say nobody wrote it.
     *
     * <p><b>The border and not the row.</b> Two rows can stop this walk at one border and a third
     * can run out, and what is owed a reader is that the border was not searched to the end. How
     * large the search was is what one row happened to hold rather than what is true of the point,
     * so a figure of it here would make two facts of one. Which figure stopped it is evidence of
     * the fact for the same reason, and two walks of one border stopped at two are one fact met at
     * both ({@code WeakeningSet}).
     *
     * @param limits how many readings of one row a point is tried against, as each stood where a
     *               walk over them stopped, each once and in {@link Figure#inOrder}
     */
    record BorderReadingsNotExhausted(souther.compiler.partition.Border border,
                                      List<Figure> limits) implements Weakening {

        public BorderReadingsNotExhausted {
            Objects.requireNonNull(border, "a walk stopped at some border");
            limits = Figure.inOrder(limits);
            if (limits.isEmpty()) {
                throw new IllegalArgumentException("a walk stopped at a limit says which");
            }
        }

        /** Stopped at one limit, which is how a walk meets it. */
        public BorderReadingsNotExhausted(souther.compiler.partition.Border border, Figure limit) {
            this(border, List.of(limit));
        }

        /** The figure is this compiler's, so a run allowed more readings comes to another answer. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.MAY_CHANGE;
        }
    }

    /**
     * A border was not held against the lines the model puts one step from it.
     *
     * <p>Beside the two above rather than among them. Those are readings of the rows that came to
     * nothing or were never made, and what they weaken is every question over those rows. This is
     * the one question over them that was not put — because the rows fall all on one side of the
     * line, because nothing watched a run, because no input that tells the lines apart could be
     * shown to arrive, or because the family could not be worked out whole.
     *
     * <p><b>So it is not a fact about the model.</b> A line one step from this one exists whichever
     * it is, and a reader told the question does not arise would be told the opposite of what
     * happened. Which it was is the word a document writes, because what to do about them differs.
     *
     * <p>The border and not the line beside it. Which lines are beside it is the family's answer and
     * is the same at every run; that this one was not held against them is the fact, and it is one
     * fact however many lines the family holds.
     */
    record ABorderNotHeldAgainstTheLinesBesideIt(souther.compiler.partition.Border border,
                                                 ABorderNotHeldAgainstTheLinesBesideIt.Why why)
            implements Weakening {

        /** What stood in the way of holding it against them. */
        public enum Why {
            /** Every row the quantity has a value at falls on one side of the line, so the rows pin
             *  no threshold on any line beside it. */
            THE_ROWS_ARE_ALL_ON_ONE_SIDE,
            /** A row was left out because nothing watched its run, so whether it reached the rule
             *  could not be told. */
            NOTHING_WATCHED_THE_RUNS,
            /** A line beside it stands after every row, and nothing here could show an input the
             *  two answer differently at that a row still arrives at. */
            NO_REACHABLE_DISTINGUISHER,
            /** A model's own decimals put a step of the fault family out of the exact arithmetic's
             *  reach, so the family this border is held against is not known whole. */
            ARITHMETIC_COULD_NOT_HOLD_A_FAMILY_MEMBER
        }

        public ABorderNotHeldAgainstTheLinesBesideIt {
            java.util.Objects.requireNonNull(border, "a border that was not held is named");
            java.util.Objects.requireNonNull(why, "a question not put says what stood in the way");
        }

        /**
         * Asked of what stood in the way, because they do not answer alike.
         *
         * <p>Rows that fall all on one side, a line no arriving input tells apart and a family the
         * arithmetic could not hold are not allowances: every run of this compiler over this model
         * says the same. What a run watched is an allowance — the arms are instrumented because a
         * build asked for them — so a run allowing more need not leave the same rows out.
         */
        @Override
        public RunSensitivity runSensitivity() {
            return switch (why) {
                case THE_ROWS_ARE_ALL_ON_ONE_SIDE,
                     NO_REACHABLE_DISTINGUISHER, ARITHMETIC_COULD_NOT_HOLD_A_FAMILY_MEMBER ->
                        RunSensitivity.UNAFFECTED;
                case NOTHING_WATCHED_THE_RUNS -> RunSensitivity.MAY_CHANGE;
            };
        }
    }

    /** The reading of the model that a measure depends on did not run out. */
    record ModelReadingIncomplete(ClosureGap cause) implements Weakening {

        /** What was still open when it stopped is what says whether a wider run closes it. */
        @Override
        public RunSensitivity runSensitivity() {
            return cause.runSensitivity();
        }
    }

    /**
     * The model gives this behavior a body, and the image the run was measured in does not carry
     * it.
     *
     * <p>The whole of what a measure knows, and nothing about how it came about. A body its own
     * rules refused, one an image left out because an implementation it reaches could not be made,
     * and a module nothing elaborated at all are one fact here — which of them it was is the
     * elaboration's answer, and a measure that named it would be reporting the route rather than
     * the hole. {@code BodyReading.NotInElaboration} is the same sentence one rung down, and this
     * is what it costs a measure.
     *
     * <p>Named by the behavior, because that is what the answer is of. Which implementations an
     * image carries is a closure over a module's implementations and is settled per behavior, so a
     * word quantified over the module says of every behavior of it something true of one — and the
     * module whose check was made in full is then reported as one that did not compile.
     */
    record BodyNotInEvaluation(String behavior) implements Weakening {

        /** Which implementations an image carries is settled by what came out, and a run under
         *  wider allowances is made in the same image. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    /**
     * The boundary of one behavior could not be worked out, so every measure that reads one is
     * short of it.
     *
     * <p>Named by the behavior and by nothing else. Both measures of a behavior's boundary go
     * without this one thing, and which of them was asking is not part of the fact — a measure
     * named beside it would turn one cause into as many facts as there are measures that read it,
     * which is counting the paths a fact arrived by ({@link WeakeningSet}).
     *
     * <p>Not the reason there is no boundary. A name that resolved to nothing is reported where it
     * was written, and this says only what that left unmeasurable.
     */
    record BoundaryNotDerived(String behavior) implements Weakening {

        /** There was no boundary to work out, which a wider run does not change: what a name
         *  resolves to is not a figure anything was compared against. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    /**
     * The input of the behavior was not read, so no measure that reads a position of it could be
     * finished.
     *
     * <p>Beside the one above rather than folded into it, because the two send a reader to
     * different places. A behavior whose boundary was not derived has a name in its own declaration
     * that resolved to nothing. This one's declaration is whole: what refused the reading is a hole
     * somewhere in the module, and the behavior it stops is any behavior the module declares.
     *
     * <p>Named by the behavior for the reason the one above is: every measure that reads a position
     * is short of this one thing, and which of them was asking is not part of the fact.
     */
    record InputNotRead(String behavior) implements Weakening {

        /** A hole in the module refused the reading, which is not a figure anything was compared
         *  against: a run that allows more meets the same hole. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    /**
     * The space of two-class combinations was too large to walk, so the counts describe part of it.
     *
     * <p>Not an observation that went missing and not a reading of the model that stopped: the model
     * was read and the rows were seen, and this measure's own enumeration is what ran out. It was
     * the one warrant a measure did carry — a {@code truncated} flag beside the status, which #951
     * had to add a constructor check to keep the two in step.
     */
    record PairSpaceTruncated(String behavior, long total, List<Figure> limits)
            implements Weakening {

        public PairSpaceTruncated {
            limits = Figure.inOrder(limits);
            if (limits.isEmpty()) {
                throw new IllegalArgumentException("a walk stopped at a limit says which");
            }
        }

        /** Stopped at one limit, which is how a walk meets it. */
        public PairSpaceTruncated(String behavior, long total, Figure limit) {
            this(behavior, total, List.of(limit));
        }

        /** The one arm that is a figure of its own. {@code limit} is what the walk was compared
         *  against, and it is a number the query graph hands the analysis, so a run under a wider
         *  {@code AdequacyPolicy} walks further. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.MAY_CHANGE;
        }
    }

    /**
     * A row went through an arm this compiler had proven nothing arrives at.
     *
     * <p>Nothing about the model is wrong here — the proof is. So this is not missing evidence: it
     * is evidence that an analysis the numbers were computed with does not hold, which is why it is
     * an arm of its own and never one of {@link ObservationIncomplete}.
     *
     * <p><b>The arm the source wrote, and not the number a run through it was recorded at.</b> Those
     * are two identities: a probe is what a recording is written in and says of itself that it
     * reaches no further, and which arm it is about is what the sites hold. The two are told apart
     * where both are in hand, which is where the arms of the behavior are, and what travels from
     * there is the one a reader can be sent to. Carried as the number, every later projection had a
     * token nobody outside the numbering could read.
     */
    record ProofContradicted(CoverageSites.Obligation arm) implements Weakening {

        /** An analysis that does not hold is one that does not hold however much a run allows. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    /**
     * A row went down a way through {@code behavior}'s body this compiler had proven no input takes
     * ({@link DecisionReading#impossible}).
     *
     * <p>The same fact as {@link ProofContradicted}, about a way rather than an arm: the proof is
     * wrong, and the rules counted are short of whatever lies past the way, since none of them was
     * read. Its own arm because what it is about is a way of the decision, which is the
     * behavior's, and no arm a reader can be sent to.
     */
    record ProofOfAWayContradicted(String behavior, DecisionRule way) implements Weakening {

        public ProofOfAWayContradicted {
            Objects.requireNonNull(behavior, "a way is some behavior's");
            Objects.requireNonNull(way, "a proof is of some way");
        }

        /** An analysis that does not hold is one that does not hold however much a run allows. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    /**
     * Two decisions of one body could not be told apart, so the arms counted as one arm are more
     * than one.
     *
     * <p>What the numbers then hold is more than they say. {@link SourceConstructOrigin} names the fork
     * within its module, so this needs nothing beside it to be a fact.
     */
    record ArmsUnsettled(SourceConstructOrigin fork) implements Weakening {

        /** Two decisions that could not be told apart are not told apart by allowing more. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    /**
     * A row of the behavior ran and this reading could not tell which rule of its decision the run
     * took.
     *
     * <p>What it takes away is the claim that a rule nothing was seen taking is a rule no row
     * takes. The row went somewhere; a rule reported as taken by nothing may be where it went, and
     * an author told to write one for it may be told to write a row that is already in the file.
     *
     * <p><b>About the reading and not about the rule.</b> Nothing here says a rule is out of reach
     * or that a row for it is owed — those are the requirement and the coverage, and each is
     * answered elsewhere. The fact is that a run this compiler watched could not be placed.
     *
     * <p>{@code why} is carried rather than counted away. A run no recognisable rule matches and a
     * run more than one matches are different shortfalls, and a reader handed only that some row
     * went unplaced has nothing to act on.
     */
    record DecisionOfRowUnreadable(String behavior,
                                   souther.compiler.partition.RulesTaken.WhichRule.Why why)
            implements Weakening {

        public DecisionOfRowUnreadable {
            java.util.Objects.requireNonNull(behavior, "a row is a row of some behavior");
            java.util.Objects.requireNonNull(why, "a reading that fell short says what stopped it");
        }

        /** A run this reading cannot place is not placed by allowing the build more. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    /**
     * A row of the behavior ran and nothing recorded where it went.
     *
     * <p>Its own word beside {@link DecisionOfRowUnreadable}, which is the nearest thing and is not
     * this: there a run was watched and no rule could be told of it, here there is nothing to tell
     * a rule of. Both leave a rule nothing was seen taking as one a row may already take, and they
     * are different shortfalls — a reader of the first goes looking at the rules, and a reader of
     * this at what read the run.
     *
     * <p>Said by the reading of the runs rather than taken from the reading of the rows. A row with
     * no account may sit in a reading of the rows that finished, so a reading that borrowed the
     * row reading's words for it had nothing to say exactly where it went without the most.
     */
    record DecisionRunNotWatched(String behavior) implements Weakening {

        public DecisionRunNotWatched {
            java.util.Objects.requireNonNull(behavior, "a row is a row of some behavior");
        }

        /** What watched a run is what this build recorded, and a wider one records no more. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    /**
     * A meeting of the body's decisions whose combinations the classes of the input do not place.
     *
     * <p>A way of settling one of its factors, or the way to it, narrows no position — the arm
     * itself, where what a run is seen doing does not tell the ways into it apart — or two ways of
     * settling one factor leave the same classes. No row can be steered into one of its
     * combinations rather than another, so none is asked for, and which of them the rows make is
     * not measured. Nothing is owed at any of them, because nothing established that a row is
     * missing.
     *
     * <p>Beside {@link MeetingsNotWalked}, which a wider run walks. This is how the body is read,
     * and allowing more reads it the same way.
     */
    record MeetingsNotPlaced(String behavior, int groups) implements Weakening {

        public MeetingsNotPlaced {
            Objects.requireNonNull(behavior, "a meeting is a meeting of some behavior");
            if (groups < 1) {
                throw new IllegalArgumentException(
                        "a measure that placed every group went without nothing here: " + groups);
            }
        }

        /** The classes place what they place however much a run allows. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    /**
     * A sum of the elements a comparison keeps whose decisions this reading met and could not join
     * to the evaluations a run records.
     *
     * <p>The sum is a meeting: each element is in it or not, and it is a function of all of them.
     * What is missing is which evaluation of the comparison a recording holds is which element's,
     * and without that no row can be held to a combination of them — an element kept by two
     * comparisons, for one, is evaluated by the second only if the first kept it. So none is asked
     * for, and which of them the rows make is not measured. Nothing is owed at any of them, because
     * nothing established that a row is missing; and a behavior is not said to have had every
     * combination of its decisions made when some of them were never asked about.
     *
     * <p>Beside {@link MeetingsNotPlaced}, which is the classes of the input not placing a group
     * this reading did form. Here there is no group: the decisions were not joined into one. The
     * reasons are {@code WhyNotJoined}'s, kept by the reading and not published.
     */
    record MeetingsNotJoined(String behavior, int groups) implements Weakening {

        public MeetingsNotJoined {
            Objects.requireNonNull(behavior, "a meeting is a meeting of some behavior");
            if (groups < 1) {
                throw new IllegalArgumentException(
                        "a measure that joined every sum went without nothing here: " + groups);
            }
        }

        /** What was joined is a matter of how the body is read, and allowing more reads it the
         *  same way. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    /**
     * A meeting of the body's decisions the measure would not walk the combinations of.
     *
     * <p>The group is read and its combinations are not enumerated, so which of them the rows make
     * is unknown — and nothing is owed at any of them, because nothing established that a row is
     * missing. What that costs is said here: a wider build would walk the group and may find a
     * combination this one never asked about.
     *
     * <p>Beside {@link PairSpaceTruncated}, which is the same figure running out on the other
     * criterion. Two words because a reader raising a limit raises a different one for each.
     *
     * @param limits what the groups held back were compared against, as each stood there: one
     *               figure handed to the run, said once however many groups it held back
     */
    record MeetingsNotWalked(String behavior, int groups, List<Figure> limits)
            implements Weakening {

        public MeetingsNotWalked {
            if (groups < 1) {
                throw new IllegalArgumentException(
                        "a measure that walked every group went without nothing here: " + groups);
            }
            limits = Figure.inOrder(limits);
            if (limits.isEmpty()) {
                throw new IllegalArgumentException("a group held back was held back by a limit");
            }
        }

        /** A figure the query graph hands the analysis, like the pair space's: a run under a wider
         *  {@code AdequacyPolicy} walks the group this one held back. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.MAY_CHANGE;
        }
    }

    /**
     * The ways through a body could not all be written down, so what rules its decision has is not
     * known.
     *
     * <p><b>Not a body that decides nothing.</b> A reading that stopped at a figure comes back with
     * none of the body's rules rather than some of them, and a reader taking that for the model's
     * answer would publish a body of many ways as one that states no decision. What is known is
     * that the derivation did not finish.
     *
     * <p>Beside {@link DecisionOfRowUnreadable} and not among it. That one is about which rule a
     * run took, with the rules in hand; this is about not having them. A reader acts on the two
     * differently — one leaves a rule undecided, and this one leaves the account without the
     * obligations to decide about.
     */
    record DecisionReadingIncomplete(
            String behavior,
            souther.compiler.partition.DecisionReading.Enumeration why) implements Weakening {

        public DecisionReadingIncomplete {
            java.util.Objects.requireNonNull(behavior, "a decision is some body's");
            java.util.Objects.requireNonNull(why, "a reading that stopped says what stopped it");
        }

        /**
         * What stopped it is a figure this reading was held to, so a reading held to a larger one
         * gets further.
         */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.MAY_CHANGE;
        }
    }

    /**
     * Some rule of the decision was read with fewer of the distinctions its way consults than the
     * body draws, so what it is was not read in full.
     *
     * <p>Beside {@link DecisionReadingIncomplete} and not one of its reasons. There the rules are not
     * in hand; here they are, and one of them is described by less than it turns on — so it may be
     * one rule where the body has two, and a run seen doing every condition it carries has not been
     * shown to have taken it. A fact about the derivation of the rules, and so a fact whether or not
     * any row ran: a behavior nobody wrote a row for is short of it exactly as much.
     *
     * <p>Of the behavior and not of a rule. Which rules it bears on is each rule's own answer
     * ({@link souther.compiler.partition.DecisionReading.Ruled#whole}), and it is asked of the rule
     * where a finding about one is made ({@link DecisionEvidence#at}).
     */
    record DecisionRuleReadShort(String behavior) implements Weakening {

        public DecisionRuleReadShort {
            java.util.Objects.requireNonNull(behavior, "a decision is some body's");
        }

        /** What the reading has no words for is not given words by allowing it more. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    /**
     * A decision of a body turns on which of several elements of one key a map filed from a list
     * holds — the last — and what that decides was not measured.
     *
     * <p>The last value for a key is read as it is: what a statement says of an entry is said of
     * the last element of its key. What is not established is that the rows tell apart what that
     * order decides — a row the statement holds of with the last element of a key the entry and
     * fails of with the first, and a row the other way round. Said where no row was seen in one of
     * the two ({@link CasesTheRowsTook}), and never where the rules of
     * the list keep its keys apart, since then no key is held twice.
     *
     * <p>About the behavior and not about a rule: the order is a property of the map the body
     * looks values up in, and each decision downstream of the lookup rests on it.
     */
    record KeyedOverwriteCasesUnmeasured(String behavior) implements Weakening {

        public KeyedOverwriteCasesUnmeasured {
            Objects.requireNonNull(behavior, "an overwrite order is that of some body's map");
        }

        /** What is missing is a row of the model's own, which a run allowed more of does not add. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    /**
     * A decision of a body turns on a search from a node for some node below it, and what that
     * decides was not measured.
     *
     * <p>The search is read as it is: what it asks of the node it starts at, and of that node having
     * nothing below. Its cases are the steps of the recursion: the node it starts at meeting what
     * it asks; that node not meeting it and one below doing so; that node not meeting it with
     * nothing below; and that node not meeting it with every child searched coming back empty.
     * This says some case the decision can come out in was not seen in any row
     * ({@link CasesTheRowsTook}).
     * About the behavior and not about a rule: every decision downstream of the search rests on
     * it.
     */
    record ReachableNodeCasesUnmeasured(String behavior) implements Weakening {

        public ReachableNodeCasesUnmeasured {
            Objects.requireNonNull(behavior, "a search is that of some body");
        }

        /** What is missing is a row of the model's own, which a run allowed more of does not add. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    /**
     * A rewrite of one behavior's body nothing here could decide about: whether a row tells it from
     * the body is not known, and not that none does.
     *
     * <p>Named by the rewrite, because each is an obligation of its own and what left one open says
     * nothing about the next. And by the module, because two modules may each declare a behavior of
     * the one name and each call the one library definition: their rewrites are the same
     * {@code Replacement} of the same behavior name, and put together would be one fact.
     */
    record RewriteUndecided(String module, String behavior, Replacement replacement,
                            ReplacementEvidence.Undecided.LeftOpen why)
            implements Weakening {

        public RewriteUndecided {
            Objects.requireNonNull(module, "a rewrite is of a body some module declares");
            Objects.requireNonNull(behavior, "a rewrite is of some behavior's body");
            Objects.requireNonNull(replacement, "a rewrite left open is some rewrite");
            Objects.requireNonNull(why, "a rewrite left open was left open for a reason");
        }

        /** Asked of the ways it was left open, each of which the place that left it open
         *  answered: a wider run could come to another answer where any of them could. */
        @Override
        public RunSensitivity runSensitivity() {
            return why.runSensitivity();
        }
    }
}
