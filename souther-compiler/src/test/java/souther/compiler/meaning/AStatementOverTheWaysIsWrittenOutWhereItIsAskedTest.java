package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A statement over the ways its elements are kept is held as how it is written out. Holding it,
 * telling it from another and denying it write nothing out; asking for its cases does, once.
 */
class AStatementOverTheWaysIsWrittenOutWhereItIsAskedTest {

    private static final Proposition CASES = new Proposition.Any(List.of(truth("a"), truth("b")));

    private static Proposition truth(String at) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(at)), true);
    }

    private static Proposition.OfTheWays over(String spelled, AtomicInteger writes) {
        return new Proposition.OfTheWays(new Proposition.WrittenWays(spelled, true, 2, () -> {
            writes.incrementAndGet();
            return CASES;
        }), true);
    }

    @Test
    void holdingAndDenyingItWriteNothingOut() {
        AtomicInteger writes = new AtomicInteger();
        Proposition.OfTheWays ways = over("ways", writes);
        assertEquals(ways, ways.denied().denied());
        assertNotEquals(ways, ways.denied());
        assertEquals(0, writes.get());
    }

    @Test
    void itsCasesAreWrittenOutOnceHoweverOftenAndWhicheverWayRoundItIsAsked() {
        AtomicInteger writes = new AtomicInteger();
        Proposition.OfTheWays ways = over("ways", writes);
        assertSame(ways.written(), ways.written());
        assertEquals(CASES.denied(), ((Proposition.OfTheWays) ways.denied()).written());
        assertEquals(1, writes.get());
    }

    @Test
    void twoStatementsAreToldApartByWhatTheirWaysAreMadeOf() {
        AtomicInteger writes = new AtomicInteger();
        assertEquals(over("ways", writes), over("ways", writes));
        assertNotEquals(over("ways", writes), over("other ways", writes));
        assertEquals(0, writes.get());
    }
}
