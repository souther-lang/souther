package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.meaning.WrittenLine;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a reader is told put things on the way to a line is what put things on that way, and not on
 * another way read with it.
 *
 * <p>One reading walks the way to a comparison and puts each case of where a line of it decides on
 * that way, and says who put each entry there of all of them together. The comparison and each
 * case are filed as lines of their own, each a way a row is looked for along; a copy told of one
 * that put something only on another, or on a case the line is no longer read in, sends a reader to
 * a call the row never goes through.
 */
class WhatPutThingsOnALinesWayIsToldOfThatWayAloneTest {

    private static ModelOccurrence copy(int ordinal) {
        return new ModelOccurrence(SourceConstructOrigin.written(new WrittenOwner.Body("m", "f"),
                ordinal, SourceConstruct.BINARY), ExpansionLineage.ORIGINAL);
    }

    private static OnTheWay entry(int ordinal) {
        ConditionOccurrence at = new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING,
                ordinal);
        return new OnTheWay.Declined(at, new ConditionReportAnchor.WhereTheReadingMetIt("m", at),
                new WhyNotTaken.OutsideDomain(WhyNotTaken.DomainLimit.A_QUANTITY_ON_NO_ORDER));
    }

    private static WhereAPartDecides aCase(String which) {
        return new WhereAPartDecides(new PlaceOfALine(PartOfAComparison.of(
                WrittenLine.THE_COMPARISON), "line"), new Proposition.Truth(
                new DecisionSubject.AnInput(TermPath.of(which)), true));
    }

    @Test
    void eachLineIsToldWhatPutThingsOnItsOwnWay() {
        ModelOccurrence states = copy(0);
        OnTheWay toTheComparison = entry(1);
        OnTheWay inOne = entry(2);
        OnTheWay inTheOther = entry(3);
        OnTheWay inACaseNotRead = entry(4);
        Map<OnTheWay, List<ModelOccurrence>> by = new LinkedHashMap<>();
        by.put(toTheComparison, List.of(copy(11)));
        by.put(inOne, List.of(copy(12)));
        by.put(inTheOther, List.of(copy(13)));
        by.put(inACaseNotRead, List.of(copy(14)));
        Map<WhereAPartDecides, List<OnTheWay>> cases = new LinkedHashMap<>();
        cases.put(aCase("one"), List.of(inOne));
        cases.put(aCase("other"), List.of(inTheOther));

        ReachingCuts.Collected collected = new ReachingCuts.Collected();
        collected.reached(states, List.of(toTheComparison), cases,
                new SaidOnTheWay(by, Map.of(), Map.of()));
        ReachingCuts made = collected.made();

        assertEquals(List.of(copy(11)), told(made, states, Optional.empty()),
                "the comparison, by what put things on the way to it");
        assertEquals(List.of(copy(11), copy(12)), told(made, states, Optional.of(aCase("one"))),
                "one case, by that and what put the case on it");
        assertEquals(List.of(copy(11), copy(13)), told(made, states,
                Optional.of(aCase("other"))), "and the other, by that and what put it on");
    }

    private static List<ModelOccurrence> told(ReachingCuts made, ModelOccurrence states,
                                              Optional<WhereAPartDecides> part) {
        return made.saidByLine().get(new ReachingCuts.ALine(states, part)).copies();
    }
}
