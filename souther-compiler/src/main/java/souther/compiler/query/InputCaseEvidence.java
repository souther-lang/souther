package souther.compiler.query;

import souther.compiler.observe.MeasureReason;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Objects;
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
                                Measure<Cases> cases) {

    /**
     * What the rows reached at this position, where anybody counted.
     *
     * <ul>
     *   <li>{@link #specified} — a row writes an input of this case, and it built.</li>
     *   <li>{@link #executed} — the behavior was applied to it.</li>
     *   <li>{@link #verified} — the row that did so held.</li>
     * </ul>
     *
     * @param unread rows whose input case could not be read, in the order they were read, each with
     *               how far its case could have got
     */
    public record Cases(Set<TypeSymbol> specified, Set<TypeSymbol> executed,
                        Set<TypeSymbol> verified, List<Unread> unread) {

        public Cases {
            specified = Evidence.ordered(specified);
            executed = Evidence.ordered(executed);
            verified = Evidence.ordered(verified);
            unread = List.copyOf(unread);
        }

        /** How many rows' case at this position could not be read: rows, and not the reasons,
         *  of which one row may have two. */
        public int unclassifiedRows() {
            return (int) unread.stream().map(each -> each.how().rowRef()).distinct().count();
        }

        /** The cases of one of the three sets. {@link Reached#NOWHERE} is none of them. */
        public Set<TypeSymbol> of(Reached set) {
            return switch (set) {
                case SPECIFIED -> specified;
                case EXECUTED -> executed;
                case VERIFIED -> verified;
                case NOWHERE -> throw new IllegalArgumentException(
                        "a row that got nowhere is in no set, so there is none to read");
            };
        }
    }

    /**
     * How far a row got at this position, which is which of the sets of {@link Cases} its case is
     * in: every set up to and including this one. One value and not a set of them, because a row
     * gets to them in order — what held was applied, and what was applied was built.
     */
    public enum Reached {
        /** Its values were never handed over, so its case is in none of them. */
        NOWHERE,
        SPECIFIED,
        EXECUTED,
        VERIFIED;

        /** The three sets, in the order a row gets to them. */
        public static final List<Reached> SETS = List.of(SPECIFIED, EXECUTED, VERIFIED);

        /** Whether a row that got this far has its case in {@code set}. */
        public boolean isIn(Reached set) {
            return set != NOWHERE && compareTo(set) >= 0;
        }
    }

    /**
     * A row whose case at this position could not be read, and how far the row got.
     *
     * @param how     why the case was not read
     * @param reached how far the row got, which is how far its case would have got had it been
     *                read
     */
    public record Unread(UnreadCase how, Reached reached) {

        public Unread {
            Objects.requireNonNull(how, "a case not read was not read for a reason");
            Objects.requireNonNull(reached, "a row got somewhere, if only nowhere");
        }

        /**
         * How far its case may have got. A row that did not finish got as far as it got for a
         * reason that is not the model's, so nothing says which sets its case stops short of: it
         * may have got to any of them.
         */
        public Reached mayReach() {
            return how instanceof UnreadCase.Stopped ? Reached.VERIFIED : reached;
        }
    }

    /** No row names this behavior. */
    public enum NoRows implements NotMeasuredReason {
        NO_ROWS;

        @Override
        public MeasureReason.About about() {
            return MeasureReason.About.THE_BEHAVIOR;
        }
    }

    /** Why one input's cases have no numbers. */
    public enum NotASum implements NotApplicableReason {
        /** The position is one data rather than a sum, so there is no case to cover. */
        NOT_A_SUM;

        @Override
        public MeasureReason.About about() {
            return MeasureReason.About.THE_BEHAVIOR;
        }
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
                new Measure.NotApplicable<>(NotASum.NOT_A_SUM));
    }

    /** Something the boundary this is read off is made of was missing, so what the position's type
     *  has was never seen. Empty here says nothing, for the reason
     *  {@link OutputCaseEvidence#notMeasurable} gives. */
    public static InputCaseEvidence notMeasurable(int at, BoundaryForMeasurement.NotDerived why,
                                                  String behavior) {
        return new InputCaseEvidence(at, Set.of(), Set.of(), why.failed(behavior));
    }

    /** The same for one input, and for the reason {@link OutputCaseEvidence#notAsked} gives. */
    public static InputCaseEvidence notAsked(int at, Set<TypeSymbol> declared,
                                             Set<TypeSymbol> excluded) {
        return declared.isEmpty() ? none(at)
                : new InputCaseEvidence(at, declared, excluded,
                        new Measurement.NotMeasured<>(NothingWasAsked.NOT_ASKED));
    }

    /** The one place the states are chosen between. What {@code observed} is for is what
     *  {@link OutputCaseEvidence#of} says. */
    public static InputCaseEvidence of(String behavior, int at, Set<TypeSymbol> declared,
                                       Set<TypeSymbol> excluded, Cases cases,
                                       boolean anyRowWasSeen, WeakeningSet observed) {
        if (declared.isEmpty()) {
            return none(at);
        }
        if (!anyRowWasSeen && observed.isEmpty()) {
            return new InputCaseEvidence(at, declared, excluded,
                    new Measurement.NotMeasured<>(NoRows.NO_ROWS));
        }
        // Only the rows whose case could still change a set. An unclassified row leaves undecided
        // a case no row is counted at (example-adequacy), so a row whose sets already hold every
        // case a row can be written at decides nothing by being read, and the count is exact
        // without it.
        // Which sets lack a case is the same question for every row, so it is asked once.
        List<Reached> lacking = cases.unread().isEmpty() ? List.of() : Reached.SETS.stream()
                .filter(set -> !missing(declared, excluded, cases.of(set)).isEmpty())
                .toList();
        List<UnreadCase> deciding = cases.unread().stream()
                .filter(each -> lacking.stream().anyMatch(each.mayReach()::isIn))
                .map(Unread::how)
                .toList();
        WeakeningSet by = deciding.isEmpty() ? observed
                : observed.union(UnreadCase.weakeningOf(deciding,
                        rows -> new Weakening.InputCasesUnreadable(behavior, at, rows)));
        return new InputCaseEvidence(at, declared, excluded, by.isEmpty()
                ? new Measurement.Complete<>(cases) : new Measurement.Partial<>(cases, by));
    }

    /** The cases of {@code declared} a row can be written at and {@code covered} does not hold. */
    private static List<TypeSymbol> missing(Set<TypeSymbol> declared, Set<TypeSymbol> excluded,
                                            Set<TypeSymbol> covered) {
        return Evidence.missingFrom(declared, covered).stream()
                .filter(each -> !excluded.contains(each)).toList();
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

    /** How many of {@link #coverable()} a row uses — see {@link Evidence#amongThem}. Throws where
     *  nothing was measured, for the reason {@link #seen()} does. */
    public int specifiedCount() {
        return Evidence.amongThem(coverable(), seen().specified());
    }

    /** Cases this input can be that no row uses, and that a row could have been written for. Empty
     *  where nothing was measured. */
    public List<TypeSymbol> unspecified() {
        return cases.made()
                .map(it -> missing(declared, excluded, it.specified()))
                .orElseGet(List::of);
    }
}
