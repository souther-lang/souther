package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ExpansionSite;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenOwner;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The helper a comparison is written in is named where a call outside every copy of it applies a
 * function to more than one element, and nowhere else. Shaped as billing writes its due dates: the
 * comparison in {@code is}, called inside the {@code find} of {@code first}, which {@code on} calls.
 */
class AHelperIsNamedWhereAFunctionAppliedOutsideItCallsItTest {

    private static final ValueName.Helper IS = new ValueName.Helper("m", "is");
    private static final ValueName.Helper FIRST = new ValueName.Helper("m", "first");
    private static final ValueName.Helper ON = new ValueName.Helper("m", "on");

    /** The copy of {@code first} the call at {@code site} made in the behavior's body, inside
     *  {@code on}'s copy. */
    private static ExpansionLineage.Expansion firstIn(int site) {
        ExpansionLineage.Expansion on = new ExpansionLineage.Expansion(ExpansionLineage.ORIGINAL,
                ON, new ExpansionSite.Written(construct(1, SourceConstruct.CALL)));
        return new ExpansionLineage.Expansion(on, FIRST,
                new ExpansionSite.Written(construct(site, SourceConstruct.CALL)));
    }

    /** The comparison in the copy of {@code is} called inside {@code first}'s copy. */
    private static ModelOccurrence comparisonIn(ExpansionLineage.Expansion first) {
        return new ModelOccurrence(construct(9, SourceConstruct.BINARY),
                new ExpansionLineage.Expansion(first, IS,
                        new ExpansionSite.Written(construct(8, SourceConstruct.CALL))));
    }

    /** The {@code find} written in {@code first}, in its copy. */
    private static ModelOccurrence findIn(ExpansionLineage.Expansion first) {
        return new ModelOccurrence(construct(7, SourceConstruct.CALL), first);
    }

    @Test
    void theHelperTheComparisonIsWrittenInIsNamedWhereAFindOutsideItAppliesItAgain() {
        ExpansionLineage.Expansion first = firstIn(2);
        assertEquals(Optional.of(new AHelperReadOnApplicationsAroundIt(IS,
                        List.of(findIn(first)))),
                AHelperReadOnApplicationsAroundIt.of(List.of(comparisonIn(first)),
                        List.of(new AHelperReadOnApplicationsAroundIt.Applied(findIn(first), 11))));
    }

    /** A copy of {@code first} on each arm of a match: each find is outside the copy of
     *  {@code is} under the other, and outside its own as well. */
    @Test
    void everyCopyIsAskedAboutAndEachCallIsNamedOnce() {
        ExpansionLineage.Expansion preceding = firstIn(2);
        ExpansionLineage.Expansion following = firstIn(3);
        assertEquals(Optional.of(List.of(findIn(preceding), findIn(following))),
                AHelperReadOnApplicationsAroundIt.of(
                                List.of(comparisonIn(preceding), comparisonIn(following)),
                                List.of(new AHelperReadOnApplicationsAroundIt.Applied(
                                                findIn(preceding), 11),
                                        new AHelperReadOnApplicationsAroundIt.Applied(
                                                findIn(following), 11),
                                        new AHelperReadOnApplicationsAroundIt.Applied(
                                                findIn(preceding), 11)))
                        .map(AHelperReadOnApplicationsAroundIt::calls));
    }

    /** The comparison written in the closure of {@code first}'s own find: declared as a behavior,
     *  {@code first} still applies it to every candidate. */
    @Test
    void aFunctionAppliedInsideTheHelpersOwnCopyNamesNothing() {
        ExpansionLineage.Expansion first = firstIn(2);
        ModelOccurrence inTheClosure = new ModelOccurrence(construct(9, SourceConstruct.BINARY),
                first);
        assertEquals(Optional.empty(), AHelperReadOnApplicationsAroundIt.of(
                List.of(inTheClosure),
                List.of(new AHelperReadOnApplicationsAroundIt.Applied(findIn(first), 11))));
    }

    /** A function applied once reads what it calls once. */
    @Test
    void aFunctionAppliedOnceNamesNothing() {
        ExpansionLineage.Expansion first = firstIn(2);
        assertEquals(Optional.empty(), AHelperReadOnApplicationsAroundIt.of(
                List.of(comparisonIn(first)),
                List.of(new AHelperReadOnApplicationsAroundIt.Applied(findIn(first), 1))));
    }

    /**
     * Of the helpers another rule suggests at the same comparison, one its copies do not stand
     * in — as billing's {@code endOfMonth} is to {@code isBusinessDay}'s comparisons — leaves it
     * read again on each application; one they stand in takes it into its own body.
     */
    @Test
    void aHelperTheCopiesDoNotStandInLeavesTheComparisonReadAgain() {
        ExpansionLineage.Expansion first = firstIn(2);
        AHelperReadOnApplicationsAroundIt named = AHelperReadOnApplicationsAroundIt.of(
                List.of(comparisonIn(first)),
                List.of(new AHelperReadOnApplicationsAroundIt.Applied(findIn(first), 11)))
                .orElseThrow();
        ValueName.Helper elsewhere = new ValueName.Helper("m", "elsewhere");
        assertEquals(List.of(elsewhere), named.leftReadAgainBy(
                List.of(elsewhere, ON, FIRST, IS), List.of(comparisonIn(first))));
    }

    @Test
    void aComparisonTheBehaviorWritesItselfNamesNothing() {
        ModelOccurrence inTheBody = new ModelOccurrence(construct(9, SourceConstruct.BINARY),
                ExpansionLineage.ORIGINAL);
        assertEquals(Optional.empty(), AHelperReadOnApplicationsAroundIt.of(List.of(inTheBody),
                List.of(new AHelperReadOnApplicationsAroundIt.Applied(
                        new ModelOccurrence(construct(7, SourceConstruct.CALL),
                                ExpansionLineage.ORIGINAL), 11))));
    }

    private static SourceConstructOrigin construct(int ordinal, SourceConstruct kind) {
        return SourceConstructOrigin.written(new WrittenOwner.Body("m", "f"), ordinal, kind);
    }
}
