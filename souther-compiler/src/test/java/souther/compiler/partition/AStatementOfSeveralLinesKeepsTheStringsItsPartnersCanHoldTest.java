package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Spelling;
import souther.compiler.meaning.WrittenLine;
import souther.compiler.values.ValueSet;

import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A place several parts of one statement are about is parted by the strings its partner can hold
 * where every part about it that parts it does so by the same strings. A part that leaves the
 * place undivided, or says nothing of any value, parts it by nothing and takes none of that away;
 * a part that is about it and does neither leaves it unparted.
 */
class AStatementOfSeveralLinesKeepsTheStringsItsPartnersCanHoldTest {

    private static final NumericTerm.ValueOf S = new NumericTerm.ValueOf(TermPath.of("s"));
    private static final List<FilingCoordinate> AT_S = List.of(FilingCoordinate.of(S));

    private static final UndividedByARelation.StringsAPartnerCanHold PARTED_BY_T =
            UndividedByARelation.StringsAPartnerCanHold.unreached(ValueSet.ANY, ValueSet.NONE,
                    null, "t");

    private static ComparisonAssessment.AgainstAnotherValue partingS() {
        return againstS(Set.of(), Map.of(S, PARTED_BY_T));
    }

    private static ComparisonAssessment.AgainstAnotherValue againstS(
            Set<FilingCoordinate> undivided,
            Map<NumericTerm.FromOnePosition, UndividedByARelation.StringsAPartnerCanHold> parted) {
        return new ComparisonAssessment.AgainstAnotherValue(AT_S, List.of(), undivided, List.of(),
                Optional.empty(), Map.of(), Map.of(), Set.of(), Map.of(), parted);
    }

    private static ComparisonAssessment.Several of(ComparisonAssessment... lines) {
        return new ComparisonAssessment.Several(Arrays.stream(lines)
                .map(line -> new ComparisonAssessment.Several.Part(new PlaceOfALine(
                        PartOfAComparison.of(WrittenLine.THE_COMPARISON), Spelling.of("line")),
                        line, List.of())).toList());
    }

    @Test
    void aPartThatPartsAPlaceAloneKeepsWhatItShows() {
        assertEquals(Map.of(S, PARTED_BY_T), of(partingS()).partnered());
    }

    @Test
    void aPartThatLeavesThePlaceUndividedTakesNothingAway() {
        assertEquals(Map.of(S, PARTED_BY_T), of(partingS(),
                againstS(Set.of(FilingCoordinate.of(S)), Map.of())).partnered());
    }

    @Test
    void aPartThatSaysNothingOfAnyValueTakesNothingAway() {
        for (ComparisonAssessment saying : List.<ComparisonAssessment>of(
                new ComparisonAssessment.RelationTurnsNothing(AT_S),
                new ComparisonAssessment.NothingArrivesAtItsRelation(AT_S),
                new ComparisonAssessment.NothingArrivesAtItsStop(AT_S))) {
            assertEquals(Map.of(S, PARTED_BY_T), of(partingS(), saying).partnered(),
                    saying.toString());
        }
    }

    @Test
    void aPartAboutThePlaceThatPartsItByNothingLeavesItUnparted() {
        assertEquals(Map.of(), of(partingS(), againstS(Set.of(), Map.of())).partnered());
    }
}
