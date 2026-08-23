package souther.compiler.query;

import souther.compiler.observe.NotApplicableReason;
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
public record OutputCaseEvidence(Set<TypeSymbol> declared, Measurement<Cases> cases) {

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
    public enum NoRows implements souther.compiler.observe.NotMeasuredReason {
        NO_ROWS
    }

    /** Why a behavior's output cases have no numbers. */
    public enum NotASum implements NotApplicableReason {
        /** The output is one data rather than a sum, so there is no case to cover and no row can
         *  fail to cover it. */
        NOT_A_SUM
    }

    public OutputCaseEvidence {
        declared = Evidence.ordered(declared);
    }

    public static OutputCaseEvidence none() {
        return new OutputCaseEvidence(Set.of(), new Measurement.NotApplicable<>(NotASum.NOT_A_SUM));
    }

    /** What the rows reached, from what they said and what could not be read of them. The one place
     *  the states are chosen between. */
    public static OutputCaseEvidence of(String behavior, Set<TypeSymbol> declared, Cases cases,
                                        boolean anyRows) {
        if (declared.isEmpty()) {
            return none();
        }
        // Nothing was read where nothing was written. Counted as a reading that found no case, this
        // said `complete` under a signature saying `no rows` — a child contradicting its parent,
        // which is the shape the whole measurement model is against.
        if (!anyRows) {
            return new OutputCaseEvidence(declared, new Measurement.NotMeasured<>(NoRows.NO_ROWS));
        }
        return new OutputCaseEvidence(declared, cases.unclassifiedRows() == 0
                ? new Measurement.Complete<>(cases)
                : new Measurement.Partial<>(cases,
                        WeakeningSet.of(new Weakening.OutputCasesUnreadable(behavior))));
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
