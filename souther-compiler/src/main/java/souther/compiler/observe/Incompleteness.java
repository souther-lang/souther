package souther.compiler.observe;

import souther.compiler.source.SourceId;

import souther.compiler.diag.Citation;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.diag.SourcePos;

import java.util.Optional;

/**
 * One reason a measure could not read everything it needed, as data rather than as a sentence.
 *
 * <p>An adequacy report is read by a build and by an agent as much as by a person, so what stopped a
 * measurement carries a code and the subject it is about. A free-text reason reads well once and
 * cannot be counted, filtered, or matched against the next run.
 *
 * @param code   what happened
 * @param target what it happened to — a behavior, a source, the module, or a position in a value —
 *               held as that thing rather than as a name beside a word for what kind of name it is.
 *               Every reader has to know whether a reason is about one behavior or about everything
 *               in a source, and while that was a guess from the shape of a string, three readers
 *               guessed differently and each was found separately
 * @param at     where, when there is a source to point at; empty for something with no position of
 *               its own, such as an invariant that arrived from a module compiled elsewhere. A
 *               {@link Citation}, so that a reason about a place says what the place is —
 *               the same question every other thing this report points at now answers
 */
public record Incompleteness(Code code, Target target, Optional<Citation> at) {

    /** What a reason is about, and so who it counts against. */
    public enum Scope {
        /** One behavior. Only that behavior's measures are affected. */
        BEHAVIOR,
        /** One source: whatever it holds, which is exactly what could not be read. */
        SOURCE,
        /** The module, and so everything in it. */
        MODULE,
        /** A position inside a value — an axis path, a field chain — and so inside one behavior. */
        POSITION,
        /** One row of one behavior, which is what the running of that row would have decided. */
        ROW
    }

    /**
     * Why a measure could not be made, and whether the rows it was to be made from were read.
     *
     * <p>Each code answers {@link #leftNoRowRead()} for itself. A reader asking whether anything
     * was read asks that rather than listing the codes that mean it: a list is a copy of this one,
     * and the copy is what a code added later is missing from.
     */
    public enum Code {
        /** A value could not be read back into an observed form at all. */
        VALUE_UNREADABLE(false),
        /** A value was larger than the limits allow, so only its shape was kept. */
        VALUE_TRUNCATED(false),
        /** A row could not be decided — it spent its budget, or the evaluation did not answer — so
         * what it would have covered is unknown. */
        ROW_UNDECIDED(false),
        /**
         * A row was not handed to what was to apply it: nothing could establish that the answer's
         * declarations are the ones the row is written for.
         *
         * <p>One code for both of the ways that happens. They are two things to tell a person — one
         * build has moved on from another, against nothing here being able to read what the answer
         * carries — and what a measure loses is the same either way: what the running would have
         * decided. Which of the two it was is said where a person reads it.
         *
         * <p>The rows behind it were read. They were built, held to their invariants, and recorded;
         * a measure over them is over rows that are there, and what is missing from it is everything
         * only the running establishes.
         */
        ANSWERER_NOT_ESTABLISHED(false),
        /**
         * The generated classes would not link.
         *
         * <p>Named for what is caught, which is a {@code LinkageError} and not one of the things
         * that raise it. The case this exists for is the runtime being off the host's classpath —
         * it is {@code provided}, like CTFE — and the JVM raises the same error for a class that
         * will not verify, one whose format it does not accept, and one compiled against a
         * different version of what it calls. Nothing here can tell them apart, so nothing here
         * says which.
         *
         * <p>One place writes it: an example whose evaluation raised one, where nothing was
         * observed and so its rows did not run. It had three, and the other two — a fill that could
         * not put its candidates through the decoder, a boundary that could not build one — are the
         * generator's to report and say so in the generator's own words. What a reader of this code
         * knows is the linking failed and that the rows behind it did not run.
         */
        LINKAGE_FAILED(true),
        /** Nothing was observed from here, so what its rows cover is unknown. */
        OBSERVATION_ABSENT(true),
        /**
         * The classes an arm-measuring evaluation needs were not made.
         *
         * <p>Named for the absence and not for any of the things that cause it — a backend that
         * failed on them, inputs that were not there — because its one producer cannot tell them
         * apart and neither can a reader of the code. A probe whose mapping was lost is one way to
         * arrive here rather than the whole of it, which is what the earlier name claimed.
         *
         * <p>Its one producer takes this branch only where arm coverage was asked for, and returns
         * no rows with it. So the request and the empty result are both part of what this says.
         */
        INSTRUMENTATION_ABSENT(true);

        private final boolean leftNoRowRead;

        Code(boolean leftNoRowRead) {
            this.leftNoRowRead = leftNoRowRead;
        }

        /**
         * Whether nothing behind this was read at all, as against read and not finished.
         *
         * <p>The difference decides who has to notice. A row that ran out of time is there and says
         * so; where nothing was read there is no row to find, and a measure over the rows that
         * remain is a measure over some of them with nothing in it to say so. A generated row is a
         * specific piece of work handed to a person, so it may not be offered from here — it may
         * already be sitting in what was not read.
         */
        public boolean leftNoRowRead() {
            return leftNoRowRead;
        }
    }

    public Incompleteness {
        at = at == null ? Optional.empty() : at;
    }

    /** Which kind of thing {@link #subject} identifies. Derived, so it cannot disagree with it. */
    public Scope scope() {
        return target.scope();
    }

    /** What it happened to, as an identity: what a build reads and what two reasons are compared on. */
    public String subject() {
        return target.subject();
    }

    /** The same, as a person is shown it — a source under the name {@code names} gives it. */
    public String shown(SourceNameResolver names) {
        return target.shown(names);
    }

    /** The source this is about, where what it names is one. Empty otherwise. */
    public Optional<SourceId> sourceIdentity() {
        return target.sourceIdentity();
    }

    /** What a whole source left unmeasured, taking the identity as one rather than as its
     *  spelling: the scope follows from the subject, so the two cannot be given disagreeing. */
    public static Incompleteness ofSource(Code code, SourceId source) {
        return new Incompleteness(code, new Target.OfSource(source), Optional.empty());
    }

    /** @throws IllegalArgumentException for a scope whose subject is not a name — a source is
     *          {@link #ofSource} and a position is {@link #atPosition} */
    public static Incompleteness of(Code code, Scope scope, String subject) {
        return new Incompleteness(code, Target.of(scope, subject), Optional.empty());
    }

    /** A reason about a place. The coordinate and not a reference over one: a reference holds a
     *  source beside the one the coordinate has, this reads the coordinate's, and a signature that
     *  still asked for the pair would let a caller write a half nothing reads.
     *
     *  @throws IllegalArgumentException for a scope whose subject is not a name, as {@link #of} */
    public static Incompleteness at(Code code, Scope scope, String subject, SourcePos where) {
        return new Incompleteness(code, Target.of(scope, subject),
                Optional.ofNullable(where).map(Citation::of));
    }

    /**
     * What one row that did not come back leaves unmeasured, read off the row.
     *
     * <p>The one place a row's outcome becomes a reason a measure could not read everything. What
     * stopped the row is a fact about the row and is written where it stopped; what a measure can
     * no longer answer is a fact about the measure. Taking the row here means the two vocabularies
     * are joined once, and means the identity and the place a reader is sent to come from the same
     * row rather than from two arguments a caller could pair wrongly.
     */
    public static Incompleteness ofRow(Code code, RowOutcome row) {
        return new Incompleteness(code, new Target.OfRow(RowRef.of(row)),
                Optional.of(souther.compiler.diag.Citation.of(row.at())));
    }

    /** A position, which takes the behavior it sits in as well as the path. Both, because whose
     * measurement it counts against is the behavior and not the path. */
    public static Incompleteness atPosition(Code code, String behavior, String path) {
        return new Incompleteness(code, new Target.AtPosition(behavior, path), Optional.empty());
    }

    /** The behavior this is about, where it is about exactly one. Empty for anything larger. */
    public Optional<String> behavior() {
        return target.onlyBehavior();
    }

    /**
     * Whether this counts against {@code behavior}, and so whether its measures stop being answers.
     *
     * <p>A reason that names one behavior answers for itself. The rest are answered here and not by
     * the target, because what a target names and what holds a behavior are two things: a module
     * holds every behavior in it by what a module is, and whether a source holds one is a fact
     * about the compilation that a source id does not carry.
     *
     * <p>A source answers yes, and that is a reading of the two places that write one. Both are a
     * source that was not evaluated at all, where which behaviors it wrote rows for is exactly what
     * could not be read — so every one of them is missing rows it may have held. A {@code SOURCE}
     * whose contents were known would need the compilation to answer and would not belong here.
     * Nothing writes one, and this is the claim to re-read if something does.
     */
    public boolean countsAgainst(String behavior) {
        return behavior().map(behavior::equals).orElse(true);
    }

    /**
     * What makes two of these the same reason: what happened, and what it happened to.
     *
     * <p>Where it was said is not part of it. A module's classes failing to be instrumented is one
     * fact however many sources went looking for them, and each of those cites it somewhere else.
     */
    public Fact identity() {
        return new Fact(code, target);
    }

    /** A reason with the place it was said left out, which is the whole of what makes two of them
     *  one. */
    public record Fact(Code code, Target target) {}
}
