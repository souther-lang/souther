package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.DeclaredInput;
import souther.compiler.inputs.ElementsMet;
import souther.compiler.inputs.InputReads;
import souther.compiler.types.Type;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A reading made at one place is taken again at another only where taking it would be the same
 * reading: it was read to the end, it left alone what it must leave alone, what it depends on
 * stands the same, and the parts it met are still met.
 *
 * <p>Each is asked of {@link SharedReads} against a scene of its own making, so that what stands
 * between a reading and being taken again is the one thing changed.
 */
class AReadingIsKeptToBeTakenAgainOnlyWhereItWouldBeTheSameReadingTest {

    private static final Core NODE = new Core.Int(1, Type.INT, new SourcePos(1, 1));
    private static final InputReads READS =
            InputReads.ofWhatIsDeclared(Map.of(), DeclaredInput.NONE);

    /** A reader whose inputs, guards and parts met are numbers and a ledger the test moves. */
    private static final class AScene
            implements SharedReads.Scene<Integer, Integer, String> {

        int input;
        int guard;
        int aggregatesAsked;
        boolean mayShare = true;
        final MetLedger<String> met = new MetLedger<>();
        boolean askedAggregatesWhenCompared;

        @Override
        public boolean mayShare() {
            return mayShare;
        }

        @Override
        public Integer inputs() {
            return input;
        }

        @Override
        public boolean sameInputs(Integer then, Integer now, boolean askedAggregates) {
            askedAggregatesWhenCompared = askedAggregates;
            return then.equals(now);
        }

        @Override
        public Integer guards() {
            return guard;
        }

        @Override
        public boolean sameGuards(Integer then, Integer now) {
            return then.equals(now);
        }

        @Override
        public ElementsMet elementsMet() {
            return ElementsMet.NONE;
        }

        @Override
        public int metCount() {
            return met.size();
        }

        @Override
        public List<String> metSince(int from) {
            return met.subList(from, met.size());
        }

        @Override
        public void meetAgain(List<String> parts) {
            met.meetAgain(parts);
        }

        @Override
        public int aggregatesAsked() {
            return aggregatesAsked;
        }
    }

    private final AScene scene = new AScene();
    private final SharedReads<Integer, Integer, String, String> reads = new SharedReads<>(scene);
    private int made;

    private String read(Object key) {
        return reads.shared(NODE, READS, key, () -> {
            made++;
            return "read";
        }, _ -> true);
    }

    @Test
    void aReadingToTheEndIsTakenAgainWhereNothingChanged() {
        read("key");
        read("key");

        assertEquals(1, made);
    }

    @Test
    void aReadingStoppedInIsNotKept() {
        reads.shared(NODE, READS, "key", () -> {
            made++;
            return "stopped";
        }, _ -> false);
        read("key");

        assertEquals(2, made, "what stopped is read again, since a reading with room may not");
    }

    @Test
    void aReadingThatChangedWhatItMustLeaveAloneIsNotKept() {
        reads.shared(NODE, READS, "key", () -> {
            made++;
            scene.guard++;
            return "read";
        }, _ -> true);
        read("key");

        assertEquals(2, made, "what it added is not there when it is taken again");
    }

    @Test
    void whatItDependsOnStandingOtherwiseIsReadAgain() {
        read("key");
        scene.input++;
        read("key");

        assertEquals(2, made);
    }

    @Test
    void anotherKeyIsAnotherReading() {
        read("one");
        read("other");

        assertEquals(2, made);
    }

    @Test
    void whereNothingMayBeSharedNothingIsKept() {
        scene.mayShare = false;
        read("key");
        read("key");

        assertEquals(2, made);
    }

    @Test
    void thePartsAWithdrawnRuleTookBackAreMetAgainWhereTheReadingIsTaken() {
        reads.shared(NODE, READS, "key", () -> {
            made++;
            scene.met.add("a part");
            return "read";
        }, _ -> true);
        scene.met.subList(0, 1).clear();
        assertEquals(List.of(), scene.met);

        read("key");

        assertEquals(1, made);
        assertEquals(List.of("a part"), scene.met,
                "met as reading it would have left them, and no more than once");
    }

    @Test
    void thePartsStillMetAreLeftWhereTheyWere() {
        reads.shared(NODE, READS, "key", () -> {
            made++;
            scene.met.add("a part");
            return "read";
        }, _ -> true);
        scene.met.add("a part met after");

        read("key");

        assertEquals(List.of("a part", "a part met after"), scene.met);
    }

    @Test
    void aReadingWhosePartsAreStillMetIsTaken() {
        reads.shared(NODE, READS, "key", () -> {
            made++;
            scene.met.add("a part");
            return "read";
        }, _ -> true);
        scene.met.add("a part of something read after");
        read("key");

        assertEquals(1, made);
    }

    @Test
    void theAggregatesAreComparedOnlyForAReadingThatAskedAfterThem() {
        reads.shared(NODE, READS, "key", () -> {
            made++;
            scene.aggregatesAsked++;
            return "read";
        }, _ -> true);
        read("key");
        assertTrue(scene.askedAggregatesWhenCompared);

        SharedReads<Integer, Integer, String, String> other = new SharedReads<>(scene);
        other.shared(NODE, READS, "key", () -> "read", _ -> true);
        other.shared(NODE, READS, "key", () -> "read", _ -> true);
        assertFalse(scene.askedAggregatesWhenCompared);
    }
}
