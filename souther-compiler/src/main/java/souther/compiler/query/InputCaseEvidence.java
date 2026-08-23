package souther.compiler.query;

import souther.compiler.observe.NotApplicableReason;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Set;

/**
 * What a behavior's {@code example} rows establish about the cases one of its inputs can be.
 *
 * <p>The counterpart of {@link OutputCaseEvidence}, and deliberately not the same type: the middle
 * slot claims something else. {@code executed} means a row applied the behavior to a value of this
 * case, not that anything was seen to come back from it.
 *
 * <p>Covering every case of an input is the mechanised half of asking whether a behavior is total:
 * every case the input can be, tried, and a result defined for it.
 *
 * @param at       which of the behavior's inputs this is, counted from zero. Held rather than left
 *                 to the index of the list these arrive in: a type that says it is the evidence of
 *                 <em>one</em> input and cannot answer which one is a value that only means
 *                 something beside the list it came from, and every reader wanting the position had
 *                 to be handed it a second time. How it is written to a person — {@code #1} for the
 *                 first — is the reader's, and a one-based number here would be this measure
 *                 spelling a report's word
 * @param declared the cases the position's type has, which is what the model says and is outside the
 *                 measurement for that reason
 * @param excluded cases the position's own rules refuse. Declared and not coverable: the type has
 *                 them and no value of one can be constructed (E1903), so they stay in
 *                 {@link #declared} because what the type can be is part of what the model says, and
 *                 they are out of {@link #coverable} because no row can be written at them. Nothing
 *                 a body declares reaches this: what leaves a denominator is what the rules refuse
 */
public record InputCaseEvidence(int at, Set<TypeSymbol> declared, Set<TypeSymbol> excluded,
                                Measurement<Cases> cases) {

    /**
     * What the rows reached at this position, where anybody counted.
     *
     * <ul>
     *   <li>{@link #specified} — a row writes an input of this case, and it built.</li>
     *   <li>{@link #executed} — the behavior was applied to it.</li>
     *   <li>{@link #verified} — the row that did so held.</li>
     * </ul>
     *
     * @param unclassifiedRows rows whose input case could not be read
     */
    public record Cases(Set<TypeSymbol> specified, Set<TypeSymbol> executed,
                        Set<TypeSymbol> verified, int unclassifiedRows) {

        public Cases {
            specified = Evidence.ordered(specified);
            executed = Evidence.ordered(executed);
            verified = Evidence.ordered(verified);
        }
    }

    /** No row names this behavior. */
    public enum NoRows implements souther.compiler.observe.NotMeasuredReason {
        NO_ROWS
    }

    /** Why one input's cases have no numbers. */
    public enum NotASum implements NotApplicableReason {
        /** The position is one data rather than a sum, so there is no case to cover. */
        NOT_A_SUM
    }

    public InputCaseEvidence {
        if (at < 0) {
            throw new IllegalArgumentException("an input at no position: " + at);
        }
        declared = Evidence.ordered(declared);
        excluded = Evidence.ordered(excluded);
    }

    /** No cases at the given input, which is what a position that is not a sum has. */
    public static InputCaseEvidence none(int at) {
        return new InputCaseEvidence(at, Set.of(), Set.of(),
                new Measurement.NotApplicable<>(NotASum.NOT_A_SUM));
    }

    /** The one place the states are chosen between. */
    public static InputCaseEvidence of(String behavior, int at, Set<TypeSymbol> declared,
                                       Set<TypeSymbol> excluded, Cases cases, boolean anyRows) {
        if (declared.isEmpty()) {
            return none(at);
        }
        if (!anyRows) {
            return new InputCaseEvidence(at, declared, excluded,
                    new Measurement.NotMeasured<>(NoRows.NO_ROWS));
        }
        return new InputCaseEvidence(at, declared, excluded, cases.unclassifiedRows() == 0
                ? new Measurement.Complete<>(cases)
                : new Measurement.Partial<>(cases,
                        WeakeningSet.of(new Weakening.InputCasesUnreadable(behavior, at))));
    }

    /** What the rows reached at this position, where a measurement was made. Throws where none was,
     *  for the reason {@link OutputCaseEvidence#seen()} gives. */
    public Cases seen() {
        return cases.made().orElseThrow(() -> new IllegalStateException(
                "an input nobody measured was read for what the rows reached: #" + at));
    }

    /** The cases a row can be written at: what the type declares, less what its rules refuse. */
    public List<TypeSymbol> coverable() {
        return declared.stream().filter(each -> !excluded.contains(each)).toList();
    }

    /** Cases this input can be that no row uses, and that a row could have been written for. Empty
     *  where nothing was measured. */
    public List<TypeSymbol> unspecified() {
        return cases.made()
                .map(it -> Evidence.missingFrom(declared, it.specified()).stream()
                        .filter(each -> !excluded.contains(each)).toList())
                .orElseGet(List::of);
    }
}
