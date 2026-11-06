package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.MeaningsOfABodyReading;
import souther.compiler.revision.RevisionKnowledge;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What each condition of a body states is read once, however many readers of the body ask.
 *
 * <p>Where a run of the body gets to and what the run meets each need it. It is the revision's
 * work, so the first of them reads every truth in the body and the other is lent that reading; a
 * key the two askings do not agree on leaves it read once per reader.
 */
class WhatABodyStatesIsReadOnceForTheReadersOfItTest {

    private static final String MODULE = "example.gate";

    private static final String MODEL = """
            module example.gate

            data Request = { rank: Int, cost: Int }
                invariant rank >= 0
                invariant cost >= 0

            data Auto
            data Manual

            behavior keep : (r: Request) -> Auto | Manual
            let keep (r) =
                if r.rank >= 3 && r.cost <= 100 then Auto else Manual

            example keep
                | "one row" : (Request { rank = 4, cost = 2 }) -> Auto
            """;

    @Test
    void theConditionsOfABodyAreReadOnceForBothReadersOfIt() {
        long before = RevisionKnowledge.timesDone(MeaningsOfABodyReading.ForOneBody.class);

        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Db db = compilation.db();

        assertTrue(db.ask(new Adequacy.PathReached(MODULE)).value().containsKey("keep"),
                "where a run of the body gets to is read");
        assertTrue(db.ask(new Adequacy.Meets(MODULE)).value().containsKey("keep"),
                "what a run of it meets is read");

        assertEquals(1, RevisionKnowledge.timesDone(MeaningsOfABodyReading.ForOneBody.class)
                        - before,
                "one body against one input, read once");
    }
}
