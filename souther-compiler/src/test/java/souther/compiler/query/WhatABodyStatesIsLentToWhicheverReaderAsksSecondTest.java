package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.meta.ModulePath;
import souther.compiler.reading.WhatABodyStates;
import souther.compiler.revision.RevisionKnowledge;

import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * What the conditions of a body state is read once for whichever of its two readers asks first,
 * once for each body, and again once an edit has moved the revision.
 *
 * <p>Where a run of the body gets to and what the run meets are the two readers. The count in
 * {@code OneMeasurementOfABehaviorReadsItsInputOnceTest} is taken after everything was answered,
 * which leaves open which of them did the work; here each order is asked outright.
 */
class WhatABodyStatesIsLentToWhicheverReaderAsksSecondTest {

    private static final String MODULE = "example.gate";

    private static final String SOURCE = "gate.sou";

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

            behavior cheap : (r: Request) -> Auto | Manual
            let cheap (r) =
                if r.cost <= 5 then Auto else Manual
            """;

    @Test
    void theReaderOfWhereARunGetsToMayAskFirst() {
        Compilation compilation = compiled(MODEL);
        long before = RevisionKnowledge.timesDone(WhatABodyStates.class);

        compilation.db().ask(new Adequacy.PathReached(MODULE));
        compilation.db().ask(new Adequacy.Meets(MODULE));

        assertEquals(2, RevisionKnowledge.timesDone(WhatABodyStates.class) - before,
                "two bodies, each read once however the two readers are ordered");
    }

    @Test
    void theReaderOfWhatARunMeetsMayAskFirst() {
        Compilation compilation = compiled(MODEL);
        long before = RevisionKnowledge.timesDone(WhatABodyStates.class);

        compilation.db().ask(new Adequacy.Meets(MODULE));
        compilation.db().ask(new Adequacy.PathReached(MODULE));

        assertEquals(2, RevisionKnowledge.timesDone(WhatABodyStates.class) - before,
                "two bodies, each read once however the two readers are ordered");
    }

    @Test
    void anEditToTheBodyIsReadAgainAndTheReaderLentTheWorkIsAnsweredOutOfIt() {
        Compilation compilation = compiled(MODEL);
        Db db = compilation.db();
        db.ask(new Adequacy.Meets(MODULE));
        db.ask(new Adequacy.PathReached(MODULE));
        Object before = db.ask(new Adequacy.Meets(MODULE)).value().get("keep");
        long done = RevisionKnowledge.timesDone(WhatABodyStates.class);

        compilation.update(Map.of(SOURCE, MODEL.replace("r.rank >= 3", "r.rank >= 5")),
                Set.of(), TestDay.DATE);
        Object after = db.ask(new Adequacy.Meets(MODULE)).value().get("keep");
        db.ask(new Adequacy.PathReached(MODULE));

        assertNotEquals(before, after, "what the run meets is read of the body as it now is");
        assertEquals(2, RevisionKnowledge.timesDone(WhatABodyStates.class) - done,
                "a revision that moved knows nothing of the last, so each body is read again, and"
                        + " once for both its readers");
    }

    private static Compilation compiled(String model) {
        return Compilation.ofDocuments(Map.of(SOURCE, model), Set.of(), ModulePath.EMPTY)
                .writtenOn(TestDay.DATE);
    }
}
