package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.check.RuleReadings;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.reading.CoverageRead;
import souther.compiler.reading.Decision;
import souther.compiler.reading.WayIn;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Which case of a sum a row taking a way can be is read off every condition on the way at once, so
 * the conditions coming in another order leave the same answer.
 *
 * <p>The body cannot be written with its conditions the other way round and the same ways: a
 * comparison after the fork has a way out of it that the other case takes. So the ways the body
 * has are read with the conditions on each of them turned round, and what the body tells apart is
 * asked again of those.
 */
class AWayIsOneChoiceOfCaseWhateverOrderItsConditionsComeInTest {

    private static final String MODEL = """
            module probe.order

            data Yes
            data No
            data Flag = Yes | No
            data Sized = { flag: Flag, amount: Int }
                invariant amount >= 0 && amount <= 1000
            data Small = { ...Sized }
                invariant amount <= 10
            data Large = { ...Sized }
                invariant amount >= 100
            data Kind = Small | Large
            data Order = { kind: Kind }

            behavior smallOnes : (o: Order) -> String
            let smallOnes (o) =
                if o.kind.amount <= 10 then
                    match o.kind.flag with
                        | Yes -> "small yes"
                        | No -> "small no"
                else "large"
            """;

    @Test
    void theConditionsTurnedRoundOnEveryWayTellTheSameApart() {
        Compilation c = Compilation.ofSource(MODEL, "Main");
        c.measure(Adequacy.Asked.fullReport());
        c.answerEverything();
        CoverageRead.Read read = c.db().ask(new Adequacy.Meets("probe.order")).value()
                .get("smallOnes");
        assertNotNull(read, () -> "the model compiles: " + c.errors());
        MeasuredInput subject = MeasuredInput.of("smallOnes",
                c.db().ask(new Adequacy.Inputs("probe.order")).value().get("smallOnes")
                        .reading(RuleReadings.of(c, "probe.order")),
                c.db().ask(new Adequacy.Divided("probe.order", "smallOnes")).value());

        Map<AxisId, BodyDistinction> asWritten = BodyDistinction.of(read, subject);
        List<WayIn> turned = new ArrayList<>();
        for (WayIn way : read.taken()) {
            turned.add(new WayIn(lastFirst(way)));
        }
        Map<AxisId, BodyDistinction> turnedRound = BodyDistinction.of(new CoverageRead.Read(
                read.interactions(), read.arms(), turned, read.restOfTheBlock()), subject);

        assertEquals(asWritten, turnedRound);
        AxisId large = subject.axes().axes().stream()
                .filter(each -> each.path().toString().equals("o.kind@Large.flag"))
                .map(Axis::id).findFirst().orElseThrow();
        assertInstanceOf(BodyDistinction.Untouched.class, turnedRound.get(large),
                () -> "no Large takes a way to the fork, in either order: " + turnedRound);
    }

    /** The decisions of a way, last first. */
    private static List<Decision> lastFirst(WayIn way) {
        return new ArrayList<>(way.decisions()).reversed();
    }
}
