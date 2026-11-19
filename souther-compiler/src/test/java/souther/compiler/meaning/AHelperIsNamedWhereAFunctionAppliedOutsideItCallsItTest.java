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
 * The helper a comparison is written in is named where a call outside a copy of it applies a
 * function around that copy more than once, and nowhere else. Shaped as billing writes its due
 * dates: the comparison in {@code is}, called inside the {@code find} of {@code first}, which
 * {@code on} calls.
 */
class AHelperIsNamedWhereAFunctionAppliedOutsideItCallsItTest {

    private static final ValueName.Helper IS = new ValueName.Helper("m", "is");
    private static final ValueName.Helper WRAP = new ValueName.Helper("m", "wrap");
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

    /** The comparison in the copy of {@code is} called inside {@code within}. */
    private static ModelOccurrence comparisonIn(ExpansionLineage within) {
        return new ModelOccurrence(construct(9, SourceConstruct.BINARY),
                new ExpansionLineage.Expansion(within, IS,
                        new ExpansionSite.Written(construct(8, SourceConstruct.CALL))));
    }

    /** The {@code find} written in {@code first}, in its copy. */
    private static ModelOccurrence findIn(ExpansionLineage.Expansion first) {
        return new ModelOccurrence(construct(7, SourceConstruct.CALL), first);
    }

    private static AHelperReadOnApplicationsAroundIt.ReadAgain read(ModelOccurrence copy,
                                                                    ModelOccurrence call,
                                                                    int applications) {
        return new AHelperReadOnApplicationsAroundIt.ReadAgain(copy, call, applications);
    }

    @Test
    void theHelperTheComparisonIsWrittenInIsNamedWhereAFindOutsideItAppliesItAgain() {
        ExpansionLineage.Expansion first = firstIn(2);
        assertEquals(Optional.of(List.of(findIn(first))), AHelperReadOnApplicationsAroundIt.of(
                List.of(read(comparisonIn(first), findIn(first), 11)))
                .map(AHelperReadOnApplicationsAroundIt::calls));
    }

    /** A copy of {@code first} on each arm of a match, each copy with its own find around it:
     *  the calls a reading at one copy stands in are that copy's alone. */
    @Test
    void aReadingAtOneCopyIsToldOfTheCallAroundThatCopyAlone() {
        ExpansionLineage.Expansion preceding = firstIn(2);
        ExpansionLineage.Expansion following = firstIn(3);
        AHelperReadOnApplicationsAroundIt named = AHelperReadOnApplicationsAroundIt.of(List.of(
                read(comparisonIn(preceding), findIn(preceding), 11),
                read(comparisonIn(following), findIn(following), 11))).orElseThrow();
        assertEquals(List.of(findIn(preceding), findIn(following)), named.calls());
        assertEquals(Optional.of(List.of(findIn(following))),
                named.restrictedTo(List.of(comparisonIn(following)))
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
                List.of(read(inTheClosure, findIn(first), 11))));
    }

    /** A function applied once reads what it calls once. */
    @Test
    void aFunctionAppliedOnceNamesNothing() {
        ExpansionLineage.Expansion first = firstIn(2);
        assertEquals(Optional.empty(), AHelperReadOnApplicationsAroundIt.of(
                List.of(read(comparisonIn(first), findIn(first), 1))));
    }

    @Test
    void aComparisonTheBehaviorWritesItselfNamesNothing() {
        ModelOccurrence inTheBody = new ModelOccurrence(construct(9, SourceConstruct.BINARY),
                ExpansionLineage.ORIGINAL);
        assertEquals(Optional.empty(), AHelperReadOnApplicationsAroundIt.of(List.of(
                read(inTheBody, new ModelOccurrence(construct(7, SourceConstruct.CALL),
                        ExpansionLineage.ORIGINAL), 11))));
    }

    /**
     * Of the helpers another rule suggests, the ones that leave the copy read again on each
     * application: one the copy does not stand in, and one the find stands in as well, which
     * takes the find into its own body with the comparison — {@code first}, and {@code on} around
     * it.
     */
    @Test
    void aHelperHoldingTheFindAsWellLeavesTheComparisonReadAgain() {
        ExpansionLineage.Expansion first = firstIn(2);
        AHelperReadOnApplicationsAroundIt named = AHelperReadOnApplicationsAroundIt.of(
                List.of(read(comparisonIn(first), findIn(first), 11))).orElseThrow();
        ValueName.Helper elsewhere = new ValueName.Helper("m", "elsewhere");
        assertEquals(List.of(elsewhere, ON, FIRST),
                named.leftReadAgainBy(List.of(elsewhere, ON, FIRST, IS)));
    }

    /** A helper between the comparison and the find, the one {@code is} is called in inside the
     *  find's closure, takes the copy out of the find's applications as {@code is} does. */
    @Test
    void aHelperTheCopyStandsInAndTheFindDoesNotTakesTheComparisonOut() {
        ExpansionLineage.Expansion first = firstIn(2);
        ExpansionLineage.Expansion wrap = new ExpansionLineage.Expansion(first, WRAP,
                new ExpansionSite.Written(construct(6, SourceConstruct.CALL)));
        AHelperReadOnApplicationsAroundIt named = AHelperReadOnApplicationsAroundIt.of(
                List.of(read(comparisonIn(wrap), findIn(first), 11))).orElseThrow();
        assertEquals(List.of(FIRST), named.leftReadAgainBy(List.of(WRAP, FIRST)));
    }

    private static SourceConstructOrigin construct(int ordinal, SourceConstruct kind) {
        return SourceConstructOrigin.written(new WrittenOwner.Body("m", "f"), ordinal, kind);
    }
}
