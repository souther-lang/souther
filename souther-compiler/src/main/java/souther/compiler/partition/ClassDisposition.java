package souther.compiler.partition;

import java.util.ArrayList;
import java.util.List;

/**
 * What the generator did about one class it was asked for.
 *
 * <p>One run's answer or what several runs came to, the same way an arm's is. A run makes one of
 * these; {@link #acrossRuns} makes the answer the runs give together, and a single run is that
 * answer already.
 *
 * <p>Which class is the key it is filed under and is not repeated here. Carried inside as well, a
 * map could hold an entry filed under one class whose value named another, and the identity a
 * reader joined a finding by would be one of two answers.
 *
 * <p>Every class the plan names has one of these. A class with none used to mean the search never
 * reached it, and what a reader made of that absence was a guess — so the absence is gone and each
 * of the ways a run declines to look says so in its own entry.
 */
public sealed interface ClassDisposition {

    /** A row was composed for it, which is this row. */
    record Built(RowId rowId) implements ClassDisposition {

        public Built {
            if (rowId == null) {
                throw new IllegalArgumentException("a class a row was composed for names the row");
            }
        }
    }

    /**
     * No row came of it, and why.
     *
     * <p>Which of the two kinds of news that is belongs to the reason and not to this. A strategy
     * took the class and composed nothing: sometimes because the rules leave no value there, which
     * a reader may act on, and sometimes because this compiler fell short, which they may not.
     * Said here as though it were always the second, a reason that settles the question would be
     * printed under a sentence denying it.
     *
     * <p>And where this compiler did fall short, what it fell short of travels with the word. A
     * class told only that a search stopped leaves an author with a shortfall of this compiler's
     * said in words they cannot act on — which is the reading the words were separated to stop,
     * one route over from where a point says the same thing and names the figure.
     */
    record Unresolved(CameToNothing came) implements ClassDisposition {

        public Unresolved {
            if (came == null) {
                throw new IllegalArgumentException("a class nothing came of says what happened");
            }
        }

        /** The words the search came back with, which is what a report prints. */
        public Generator.UnresolvedCombination why() {
            return came.why();
        }
    }

    /**
     * What the runs of one plan say about one class together.
     *
     * <p>A behavior whose dependencies a way leaves open is searched once per way of standing them
     * in, and the answer about the model is what all of those came to. Which payload survives that
     * is decided here, beside the answers a run gives, rather than wherever the runs happen to be
     * walked — so a case added below has to say what it is over the runs before anything compiles.
     *
     * <p>No row of this is a row of the fill. A run numbers its rows among its own, so the row a
     * witness names means something only beside the run that composed it; the number a reader is
     * offered it under is given when the witnesses are materialised.
     */
    sealed interface AcrossRuns {

        /**
         * Some run composed a row, which is the answer about the model however many did.
         *
         * @param witnesses every run that composed one, in the order the runs were made. Which of
         *                  them a reader is offered is settled where they are materialised, so this
         *                  holds all of them and chooses none
         */
        record Built(List<Witness> witnesses) implements AcrossRuns {

            public Built {
                witnesses = List.copyOf(witnesses);
                if (witnesses.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a class answered by a row names the run that composed it");
                }
            }
        }

        /**
         * No run composed one, and the reason they all give.
         *
         * <p>One reason and not a list of them, because what a run stands the dependencies in with
         * reaches a composed row and decides nothing about whether a value builds or what a refusal
         * says. The runs agree here or the search has come to depend on something this says it does
         * not, which is why {@link #acrossRuns} refuses a disagreement rather than picking.
         */
        record Unresolved(CameToNothing came) implements AcrossRuns {

            public Unresolved {
                if (came == null) {
                    throw new IllegalArgumentException("a class nothing came of says what happened");
                }
            }

            /** The words every run came back with, which is what a report prints. */
            public Generator.UnresolvedCombination why() {
                return came.why();
            }
        }

        /** A run that composed a row, and the row it composed, kept together as one answer. */
        record Witness(int run, ClassDisposition.Built built) {

            public Witness {
                if (built == null) {
                    throw new IllegalArgumentException("a witness is a run and what it composed");
                }
            }
        }
    }

    /**
     * The answer the runs of one plan give about one class.
     *
     * <p>A row wherever any run composed one. Where none did, the reason every one of them gives,
     * and they have to be the same reason: a run reaching a different one would mean what it stood
     * the dependencies in with had decided whether a value can be built, and a reader would be
     * shown whichever way the ways were enumerated.
     *
     * <p>What the runs met of this compiler's is added up instead of held to agreeing. That is how
     * far each run got and not what any of them says about the model, so a figure one run reached
     * is a figure somebody can raise however far the next run went.
     *
     * @param runs what each run did, in the order the runs were made
     */
    static AcrossRuns acrossRuns(List<ClassDisposition> runs) {
        if (runs.isEmpty()) {
            throw new IllegalArgumentException("no run was asked about this class");
        }
        List<AcrossRuns.Witness> witnesses = new ArrayList<>();
        List<CameToNothing> came = new ArrayList<>();
        for (int run = 0; run < runs.size(); run++) {
            switch (runs.get(run)) {
                case ClassDisposition.Built built ->
                        witnesses.add(new AcrossRuns.Witness(run, built));
                case ClassDisposition.Unresolved none -> came.add(none.came());
            }
        }
        if (!witnesses.isEmpty()) {
            return new AcrossRuns.Built(witnesses);
        }
        // The one law for putting two of these together, and the reason a class holds the runs to
        // one answer where an arm does not: what a class came to is one answer about the model, so
        // the words have to agree — and once they do, this is the law joining them
        // ({@link CameToNothing#joined}), which adds up what each run met rather than making a
        // second answer of it.
        List<CameToNothing> agreed = CameToNothing.joined(came);
        if (agreed.size() > 1) {
            throw new IllegalStateException(
                    "two runs of one plan give a class different reasons for having no row: "
                            + agreed.stream().map(CameToNothing::why).toList());
        }
        return new AcrossRuns.Unresolved(agreed.getFirst());
    }
}
