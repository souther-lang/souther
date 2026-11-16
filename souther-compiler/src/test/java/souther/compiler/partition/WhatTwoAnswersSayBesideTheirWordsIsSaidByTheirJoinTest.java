package souther.compiler.partition;

import net.unit8.notation199x.pattern.Meter;
import org.junit.jupiter.api.Test;
import souther.compiler.execute.RunStop;
import souther.compiler.inputs.TermPath;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Optional;
import java.util.SequencedMap;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What an answer says beside its word, where an offer was short of a rule and where runs stopped,
 * is what every search it is the join of said: the earlier's is not lost behind the later's.
 */
class WhatTwoAnswersSayBesideTheirWordsIsSaidByTheirJoinTest {

    private static final WhereARunStopped STOPPED = new WhereARunStopped(
            new RunStop.AtAConstruction("demo", "Positive", Optional.empty(), 0, Optional.empty()),
            Optional.empty());

    private static final StringOfferShortfall SHORT = StringOfferShortfall.of(
            new StringOfferShortfall.NotOffered(new StringOfferShortfall.Subject.ComposingAValue(),
                    new StringOfferShortfall.Why.TooCostly(Meter.Stopped.THE_ANSWER)));

    private static BesideTheWord shortAt(String position) {
        SequencedMap<TermPath, StringOfferShortfall> at = new LinkedHashMap<>();
        at.put(TermPath.of(position), SHORT);
        return BesideTheWord.shortOf(at);
    }

    @Test
    void theOfferTheEarlierWasShortOfIsKept() {
        BesideTheWord both = shortAt("a").and(shortAt("b"));

        assertEquals(List.of(TermPath.of("a"), TermPath.of("b")), List.copyOf(both.shortOf().keySet()));
    }

    @Test
    void whereTheRunsOfTheEarlierStoppedIsKept() {
        BesideTheWord earlier = BesideTheWord.NOTHING.stopping(List.of(STOPPED));

        assertEquals(List.of(STOPPED), earlier.and(shortAt("b")).stopped());
    }
}
