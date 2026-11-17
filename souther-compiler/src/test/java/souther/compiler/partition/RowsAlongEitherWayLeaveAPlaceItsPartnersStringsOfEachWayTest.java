package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.partition.UndividedByARelation.StringsAPartnerCanHold;
import souther.compiler.partition.UndividedByARelation.WhatItLeaves;
import souther.compiler.values.ValueSet;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A relation read along two ways leaves a string position what both leave it. Each way that parts
 * it by the strings its partner can hold is a way of its own, ways showing the same strings are one,
 * a way that leaves it undivided at every value takes none of the other's strings away, and a way
 * that shows nothing of it leaves it unparted.
 */
class RowsAlongEitherWayLeaveAPlaceItsPartnersStringsOfEachWayTest {

    private static final NumericTerm.ValueOf S = new NumericTerm.ValueOf(TermPath.of("s"));
    private static final FilingCoordinate AT_S = FilingCoordinate.of(S);

    private static final StringsAPartnerCanHold BY_T =
            StringsAPartnerCanHold.unreached(ValueSet.ANY, ValueSet.NONE, "t");
    private static final StringsAPartnerCanHold BY_U =
            StringsAPartnerCanHold.unreached(ValueSet.NONE, ValueSet.ANY, "u");

    private static WhatItLeaves parted(StringsAPartnerCanHold... by) {
        return new WhatItLeaves(Set.of(), Map.of(), true, Set.of(), Set.of(), Set.of(),
                Map.of(S, List.of(by)));
    }

    private static WhatItLeaves undivided(Set<FilingCoordinate> mayStopBefore) {
        return new WhatItLeaves(Set.of(AT_S), Map.of(), true, Set.of(), Set.of(),
                mayStopBefore, Map.of());
    }

    @Test
    void waysPartingAPlaceByDifferentStringsAreKeptEachItsOwn() {
        assertEquals(Map.of(S, List.of(BY_T, BY_U)),
                parted(BY_T).alongBoth(parted(BY_U)).partnered());
    }

    @Test
    void waysPartingAPlaceByTheSameStringsAreOneWay() {
        StringsAPartnerCanHold again =
                StringsAPartnerCanHold.unreached(ValueSet.ANY, ValueSet.NONE, "v");
        assertEquals(Map.of(S, List.of(BY_T.orAnother(again))),
                parted(BY_T).alongBoth(parted(again)).partnered());
    }

    @Test
    void aWayLeavingThePlaceUndividedAtEveryValueTakesNothingAwayFromEitherSide() {
        assertEquals(Map.of(S, List.of(BY_T)),
                parted(BY_T).alongBoth(undivided(Set.of())).partnered());
        assertEquals(Map.of(S, List.of(BY_T)),
                undivided(Set.of()).alongBoth(parted(BY_T)).partnered());
        assertEquals(Set.of(),
                parted(BY_T).alongBoth(undivided(Set.of())).undivided());
    }

    @Test
    void aWayLeavingThePlaceUndividedWhereEveryValueMayNotGetThereDoesNotKeepIt() {
        assertEquals(Map.of(), parted(BY_T).alongBoth(undivided(Set.of(AT_S))).partnered());
        assertEquals(Map.of(), undivided(Set.of(AT_S)).alongBoth(parted(BY_T)).partnered());
    }

    @Test
    void aWayShowingNothingOfThePlaceLeavesItUnparted() {
        WhatItLeaves nothing = new WhatItLeaves(Set.of(), Map.of());
        assertEquals(Map.of(), parted(BY_T).alongBoth(nothing).partnered());
        assertEquals(Map.of(), nothing.alongBoth(parted(BY_T)).partnered());
    }
}
