package souther.compiler.partition;

import souther.compiler.reading.PathAccess;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.SequencedSet;

/**
 * What the generator did about one arm it was asked for.
 *
 * <p>One run's answer or what several runs came to, since the two say the same kind of thing about
 * the same arm and a reader acts on either the same way. A run makes one of these; {@link
 * #acrossRuns} makes the answer the runs give together, and a single run is that answer already.
 * What the two are not free to share is a payload whose meaning turns on which of them it is, which
 * is why the fold over the runs has a value of its own to say what it found.
 *
 * <p>Which arm is the key it is filed under, the same way a class's is.
 *
 * <p>Three answers because they are three pieces of news. A row was composed; there is a reason
 * there is none; or there was nowhere to look at all, which the reading of the body settles and no
 * search is involved in. Told as one, a reader could not tell an arm the model refuses from one
 * this compiler could not state a way into.
 */
public sealed interface ArmDisposition {

    /**
     * A row was composed for a combination that takes it, or along the way into it.
     *
     * @param rowId which row
     * @param at    which place a run through the arm it was steered to is recorded at. An arm the
     *              author wrote stands in the running tree once per call site of the helper
     *              carrying it, and the row went down one of them — so a reader naming another
     *              would say the row does what it does not
     */
    record Built(RowId rowId, souther.compiler.coverage.ArmProbe at) implements ArmDisposition {

        public Built {
            if (rowId == null || at == null) {
                throw new IllegalArgumentException(
                        "an arm a row was composed for names the row and where it went");
            }
        }
    }

    /**
     * No row, and the reasons there is none.
     *
     * <p>Not only the reasons a search came back with. A run that never searched has one too — the
     * rows could not be read, the classes would not link — and it is as much an answer about this
     * arm as a refusal is. What this says is that there is no row and that the run can say why;
     * whether anything was tried is in the words, where {@code THE_ROWS_WERE_NOT_READ} and
     * {@code LINKAGE_FAILED} say it outright.
     *
     * <p>All of the reasons, because they are not one fact. One place stopping at the search's
     * budget and another the model's own rules refuse are different news — the first says a row may
     * still be writable and the second says the model settles it — and the arm is answered by the
     * whole of what was tried rather than by whichever was walked first.
     */
    record Unresolved(List<CameToNothing> why) implements ArmDisposition {

        public Unresolved {
            // Each word once, with what the searches that came back with it met added up
            // ({@link CameToNothing#joined}). An arm stands in several places and is looked for at
            // each, so one word arrives from more than one of them — and two answers under one
            // word would be one arm reported twice with half the figures apiece.
            why = CameToNothing.joined(why);
            if (why.isEmpty()) {
                throw new IllegalArgumentException(
                        "an arm with no row and no reason for it is one nothing answered for");
            }
        }
    }

    /**
     * Nothing was tried, because the reading of the body has no way into this arm to try.
     *
     * <p>Which is two pieces of news and the reading says which: no run reaches the arm at all, or
     * this compiler cannot state what steers a row there. Neither is a search that failed, and
     * carrying either as one would tell a reader a value was looked for.
     *
     * <p><b>What the reading made of every place the arm stands in, and not one of them.</b> An arm
     * the author wrote stands in the running tree once per call site of the helper carrying it, and
     * the two are read separately: one splice may be somewhere the model proves no run reaches
     * while another is somewhere this compiler cannot name the way to. Carrying one, the answer was
     * whichever place the walk wrote first, and swapping two call sites of one body changed a fact
     * about the model into a shortfall of ours.
     *
     * @param access what the reading made of each place, each kind of answer once and in the order
     *               the plan records the places in
     */
    record NoWayIn(List<PathAccess> access) implements ArmDisposition {

        public NoWayIn {
            access = List.copyOf(access);
            if (access.isEmpty()) {
                throw new IllegalArgumentException(
                        "an arm nothing was tried at says what the reading made of it");
            }
            if (access.stream().anyMatch(PathAccess.Ways.class::isInstance)) {
                throw new IllegalArgumentException(
                        "an arm with ways into it is one this search had somewhere to look");
            }
        }

        /** An arm the caller has one place for, which is what a search stood up on its own has. */
        public NoWayIn(PathAccess access) {
            this(List.of(access));
        }

        /**
         * Whether the model settles every place of this arm, which is what says a reader may act
         * on it.
         *
         * <p>All of them and not any: a place this compiler could not read the way to is a place a
         * row may yet be written for, so one of those leaves the arm this compiler's shortfall
         * however many of the rest the model refuses.
         */
        public boolean theModelSettlesIt() {
            return access.stream().allMatch(PathAccess.Unreachable.class::isInstance);
        }
    }

    /**
     * What the runs of one plan say about one arm together.
     *
     * <p>The second of the two folds an arm's answer is made by. {@link Generator} makes each run's
     * answer over the places the arm stands in; this makes one answer over the runs. They are not
     * the same operation, and a payload that is all of something over the places may be one thing
     * over the runs or many — which is said here, case by case, rather than worked out wherever the
     * runs are walked.
     *
     * <p>No row of this is a row of the fill, the same way a class's is not.
     */
    sealed interface AcrossRuns {

        /**
         * Some run composed a row, which is the answer about the model however many did.
         *
         * @param witnesses every run that composed one, in the order the runs were made, each
         *                  holding the whole of what that run answered with. The row and the place
         *                  it went through are one answer of one run, and a reader given the row of
         *                  one beside the place of another would be told a row goes somewhere it
         *                  does not
         */
        record Built(List<Witness> witnesses) implements AcrossRuns {

            public Built {
                witnesses = List.copyOf(witnesses);
                if (witnesses.isEmpty()) {
                    throw new IllegalArgumentException(
                            "an arm answered by a row names the run that composed it");
                }
            }
        }

        /**
         * No run composed one, and the whole of what they made of it.
         *
         * <p>All of the reasons, the way one run holds all of the reasons its places gave. A budget
         * one run stopped at and a rule another run's values were refused by are different news,
         * and the arm is answered by what was tried rather than by whichever run was made first.
         *
         * <p>Held as a set, so that what the runs came to does not depend on the order they came in
         * while the order a reader is shown them in stays the one they were first met in.
         *
         * <p>Put together before it is held, and not by being held. What each run met under one
         * word is added up ({@link CameToNothing#joined}) and what is left is one answer per word,
         * which a set then holds without anything of a run's to lose. Held first and joined by
         * whether the whole answer was equal, two runs that met different figures on the way to one
         * word would be two answers, and a reader would act on half the figures twice.
         */
        record Unresolved(SequencedSet<CameToNothing> why)
                implements AcrossRuns {

            public Unresolved {
                why = Collections.unmodifiableSequencedSet(
                        new LinkedHashSet<>(CameToNothing.joined(why)));
                if (why.isEmpty()) {
                    throw new IllegalArgumentException(
                            "an arm with no row and no reason for it is one nothing answered for");
                }
            }
        }

        /**
         * No run had anywhere to look, and what the reading made of the places.
         *
         * <p>One value the runs share rather than something joined out of several. What the reading
         * makes of a place is read off the body and the plan, which no run's stand-ins reach, so
         * two runs differing here would mean the reading had come to depend on what a run was
         * given — which {@link #acrossRuns} refuses rather than picking one of.
         *
         * <p>What a run stands the dependencies in with does decide whether anything <em>reaches</em>
         * the arm, which is why this is the answer only where no run composed a row. A row composed
         * for something else is watched, and the arms its run went through are arms a row goes
         * through however little a way into them could be named.
         */
        record NoWayIn(List<PathAccess> access) implements AcrossRuns {

            public NoWayIn {
                access = List.copyOf(access);
                if (access.isEmpty()) {
                    throw new IllegalArgumentException(
                            "an arm nothing was tried at says what the reading made of it");
                }
            }
        }

        /** A run that composed a row, and what it composed, kept together as one answer. */
        record Witness(int run, ArmDisposition.Built built) {

            public Witness {
                if (built == null) {
                    throw new IllegalArgumentException("a witness is a run and what it composed");
                }
            }
        }
    }

    /**
     * The answer the runs of one plan give about one arm.
     *
     * <p>A row wherever any run composed one. A run reaches an arm by composing a row steered
     * there or by watching a row composed for something else go through it, and the second depends
     * on what the run stood the dependencies in with — so an arm one run had nowhere to look for
     * and another was seen going through is answered by the row, and the runs are not in
     * disagreement about anything.
     *
     * <p>Where no run composed one, the whole of what they made of it; and where none of them made
     * anything of it, what the reading says. The reading is the same for every run, so the last two
     * do not mix and the readings do not differ: an arm nothing can be steered to is one nothing
     * can have failed at, and a run that says otherwise has read the body by what it was given.
     *
     * @param runs what each run did, in the order the runs were made
     */
    static AcrossRuns acrossRuns(List<ArmDisposition> runs) {
        if (runs.isEmpty()) {
            throw new IllegalArgumentException("no run was asked about this arm");
        }
        List<AcrossRuns.Witness> witnesses = new ArrayList<>();
        List<CameToNothing> why = new ArrayList<>();
        ArmDisposition.NoWayIn nowhere = null;
        for (int run = 0; run < runs.size(); run++) {
            switch (runs.get(run)) {
                case ArmDisposition.Built built ->
                        witnesses.add(new AcrossRuns.Witness(run, built));
                case ArmDisposition.Unresolved(List<CameToNothing> reasons) ->
                        why.addAll(reasons);
                case ArmDisposition.NoWayIn none -> {
                    if (nowhere != null && !nowhere.equals(none)) {
                        throw new IllegalStateException(
                                "two runs of one plan read an arm nothing was tried at differently:"
                                        + " " + nowhere.access() + " and " + none.access());
                    }
                    nowhere = none;
                }
            }
        }
        // Asked of every run and not only of the ones with no row between them. What a reading
        // gives a run to try does not turn on whether a third run composed something, so a
        // contradiction here is one whichever answer the arm ends up with.
        if (nowhere != null && !why.isEmpty()) {
            throw new IllegalStateException(
                    "one run of a plan had nowhere to look for a row for an arm and another had a"
                            + " reason for finding none: nowhere at " + nowhere.access()
                            + ", reasons " + why);
        }
        if (!witnesses.isEmpty()) {
            return new AcrossRuns.Built(witnesses);
        }
        return nowhere == null
                ? new AcrossRuns.Unresolved(new LinkedHashSet<>(why))
                : new AcrossRuns.NoWayIn(nowhere.access());
    }
}
