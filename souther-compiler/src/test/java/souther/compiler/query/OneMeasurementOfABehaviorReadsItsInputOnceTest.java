package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.AnInputRead;
import souther.compiler.revision.RevisionKnowledge;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every measure of one behavior reads its input through one reading.
 *
 * <p>The division, the subject a row is written for, the meetings the body holds and the decisions
 * it makes are questions apart, and each of them needs the input read. Read at each, every rule of
 * every parameter is read again to the answers the first reading came to. So the reading is the
 * revision's work, and this holds to what that makes true: however many of them ask, the input is
 * read for the first and lent to the rest.
 *
 * <p>Which methods read an input at all is the architecture's to say
 * ({@code WhoReadsAnInputIsWrittenDownTest}); a measure reading the input for itself passes this,
 * since nothing it did was the revision's work. What this catches is the work done once per asking
 * — a key that two askings do not agree on.
 */
class OneMeasurementOfABehaviorReadsItsInputOnceTest {

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
    void theInputIsReadOnceForEveryMeasureOfTheBehavior() {
        long before = RevisionKnowledge.timesDone(AnInputRead.class);

        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Db db = compilation.db();

        // Each measure asked outright, so that a report that stopped asking one of them leaves this
        // failing on the measure rather than passing on fewer askings.
        assertNotNull(db.ask(new Adequacy.Divided(MODULE, "keep")).value(),
                "the behavior is divided");
        assertTrue(db.ask(new Adequacy.Meets(MODULE)).value().containsKey("keep"),
                "its body's meetings are read");
        assertTrue(db.ask(new Adequacy.DecisionReadings(MODULE)).value().containsKey("keep"),
                "its decisions are read");
        assertNotNull(db.ask(new Adequacy.Generated(MODULE, "keep")).value(),
                "and rows are written for it, which takes the subject");

        assertEquals(1, RevisionKnowledge.timesDone(AnInputRead.class) - before,
                "one behavior, one reading of its input");
    }
}
