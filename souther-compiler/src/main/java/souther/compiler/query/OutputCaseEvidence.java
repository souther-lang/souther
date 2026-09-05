package souther.compiler.query;

import souther.compiler.observe.MeasureReason;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Set;

/**
 * What a behavior's {@code example} rows establish about the cases it can answer with.
 *
 * <p>{@link #declared} is outside the measurement: which cases the output type has is what the model
 * says, and it is so whether or not anybody wrote a row. What the rows established is inside, and a
 * behavior whose output is not a sum has none of it rather than having empty sets — which is the
 * same fact as "no row reached any case", written in the same bytes.
 *
 * @param declared the cases the output type has. Empty where the output is one data rather than a
 *                 sum, which is what leaves this measure nothing to be about
 */
public record OutputCaseEvidence(Set<TypeSymbol> declared, Measure<Cases> cases) {

    /**
     * What the rows reached, where anybody counted.
     *
     * <p>Three sets rather than one, because how far a row got decides what it proves.
     *
     * <ul>
     *   <li>{@link #specified} — a row expects this case. Somebody wrote down that the model owes
     *       it.</li>
     *   <li>{@link #observed} — the behavior was seen to answer with this case. A row that expected
     *       something else still saw what it saw: expecting {@code Approved} and getting
     *       {@code Rejected} is no evidence for {@code Approved} and is evidence that
     *       {@code Rejected} can happen.</li>
     *   <li>{@link #verified} — a row expected this case and the behavior produced it.</li>
     * </ul>
     *
     * <p>A behavior with no {@code let} can reach {@link #specified} and no further, which is the
     * honest account of a model that has been described and not yet written.
     *
     * @param unclassifiedRows rows whose case could not be read. While this is above zero a missing
     *                         case is undecided rather than missing, because one of those rows may
     *                         cover it — and the measurement around it says so rather than leaving a
     *                         reader to compare this with zero
     * @param answeredRows     rows the behavior answered for. Not the size of {@link #observed}: an
     *                         answer of a type no declaration names is an answer this cannot place,
     *                         so a run that got one has an empty {@code observed} and a count above
     *                         zero. What separates a run that produced nothing from one whose
     *                         answers could not be named is this, and neither of the case sets says
     *                         it.
     */
    public record Cases(Set<TypeSymbol> specified, Set<TypeSymbol> observed,
                        Set<TypeSymbol> verified, int unclassifiedRows, int answeredRows) {

        public Cases {
            specified = Evidence.ordered(specified);
            observed = Evidence.ordered(observed);
            verified = Evidence.ordered(verified);
        }
    }

    /** No row names this behavior, so nothing was established about its cases either way. */
    public enum NoRows implements NotMeasuredReason {
        NO_ROWS;

        @Override
        public MeasureReason.About about() {
            return MeasureReason.About.THE_BEHAVIOR;
        }
    }

    /** Why a behavior's output cases have no numbers. */
    public enum NotASum implements NotApplicableReason {
        /** The output is one data rather than a sum, so there is no case to cover and no row can
         *  fail to cover it. */
        NOT_A_SUM;

        @Override
        public MeasureReason.About about() {
            return MeasureReason.About.THE_BEHAVIOR;
        }
    }

    public OutputCaseEvidence {
        declared = Evidence.ordered(declared);
    }

    public static OutputCaseEvidence none() {
        return new OutputCaseEvidence(Set.of(), new Measure.NotApplicable<>(NotASum.NOT_A_SUM));
    }

    /**
     * The boundary this is read off was not worked out, so what the output type has was never seen.
     *
     * <p>{@link #declared} is empty here and says nothing by being so. Which of the ways a case set
     * comes out empty this is, is the measurement beside it: {@link NotASum} is a type that was read
     * and holds one case, and it is a reason rather than something read back off the set for exactly
     * this — a set nobody filled in and a set there was nothing to fill in with are the same bytes.
     */
    public static OutputCaseEvidence notMeasurable(BoundaryForMeasurement.NotDerived why,
                                                   String behavior) {
        return new OutputCaseEvidence(Set.of(), why.failed(behavior));
    }


    /** What the model declares, with nothing counted against it, for a build that asked for no
     *  measurement. Made here rather than by emptying a measurement above, because this is where the
     *  states are chosen between and a parent that overwrote its children would be a document whose
     *  cases say `complete` under a signature that says nobody measured. */
    public static OutputCaseEvidence notAsked(Set<TypeSymbol> declared) {
        return declared.isEmpty() ? none()
                : new OutputCaseEvidence(declared,
                        new Measurement.NotMeasured<>(NothingWasAsked.NOT_ASKED));
    }

    /**
     * What the rows reached, from what they said and what could not be read of them. The one place
     * the states are chosen between.
     *
     * @param anyRowWasSeen whether anything was observed here at all
     * @param observed      what the rows this was counted over went without: a source none of whose
     *                      rows were seen may hold the row that covers a case, so a count taken over
     *                      what remains is a count over some of them. It reaches this measure rather
     *                      than only the signature above it, because it is this measure's numbers it
     *                      makes weaker — read only above, a case set could say {@code complete}
     *                      under a signature saying it went without something, and a child
     *                      contradicting its parent is what this whole model is against
     */
    public static OutputCaseEvidence of(String behavior, Set<TypeSymbol> declared, Cases cases,
                                        boolean anyRowWasSeen, WeakeningSet observed) {
        if (declared.isEmpty()) {
            return none();
        }
        // Nothing was written and nothing went missing, so nobody counted and nobody was going to.
        if (!anyRowWasSeen && observed.isEmpty()) {
            return new OutputCaseEvidence(declared, new Measurement.NotMeasured<>(NoRows.NO_ROWS));
        }
        WeakeningSet by = cases.unclassifiedRows() == 0 ? observed
                : observed.union(WeakeningSet.of(new Weakening.OutputCasesUnreadable(behavior)));
        return new OutputCaseEvidence(declared, by.isEmpty()
                ? new Measurement.Complete<>(cases) : new Measurement.Partial<>(cases, by));
    }

    /** What the rows reached, where a measurement was made. Throws where none was: a measure with
     *  no number has none, and answering with empty sets would read as a behavior nothing covered. */
    public Cases seen() {
        return cases.made().orElseThrow(() -> new IllegalStateException(
                "an output nobody measured was read for what the rows reached"));
    }

    /** Cases the behavior can answer with that no row expects. Empty where nothing was measured: an
     *  absence of evidence is not a set of gaps. */
    public List<TypeSymbol> unspecified() {
        return cases.made().map(it -> Evidence.missingFrom(declared, it.specified()))
                .orElseGet(List::of);
    }

    /** Cases no row has confirmed the behavior answers with. */
    public List<TypeSymbol> unverified() {
        return cases.made().map(it -> Evidence.missingFrom(declared, it.verified()))
                .orElseGet(List::of);
    }
}
