package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two asks that reach one value are one location, whether or not they are spelled the same.
 *
 * <p>A row writes one value at a location, and a location holding another is not a second one: a
 * container written whole and a position inside it are the same value asked for twice. Told apart by
 * the spelling alone, both asks are taken, the composer writes whichever it plans and the point is
 * offered half-answered — the shape this class already refuses where the two paths are equal.
 *
 * <p>What comes back is that nothing here composes one, and not that no such value exists. A
 * container answering both asks is a value a model may well have; what this compiler has no way to
 * do is compose a whole value and a value inside it into one write.
 */
class AWriteInsideAnotherIsOneLocationTest {

    private static final TermPath LINES = TermPath.of("lines");

    private static final TermPath AN_AMOUNT = LINES.element().then("amount");

    private static final List<FixtureTemplate> A_VALUE = List.of(FixtureTemplate.integer(1));

    private static final List<FixtureTemplate> ANOTHER = List.of(FixtureTemplate.integer(2));

    @Test
    void aValueInsideOneAlreadyWrittenConflicts() {
        LocationWrites writes = new LocationWrites();
        assertEquals(LocationWrites.Written.FIRST, writes.write(LINES, A_VALUE));
        assertEquals(LocationWrites.Written.CONFLICTING, writes.write(AN_AMOUNT, ANOTHER),
                "the container was written whole, so a position inside it is the same value asked"
                        + " for a second time");
    }

    @Test
    void aValueAroundOneAlreadyWrittenConflicts() {
        LocationWrites writes = new LocationWrites();
        assertEquals(LocationWrites.Written.FIRST, writes.write(AN_AMOUNT, A_VALUE));
        assertEquals(LocationWrites.Written.CONFLICTING, writes.write(LINES, ANOTHER),
                "and the order the two arrive in says nothing about whether they are one location");
    }

    @Test
    void theSameAskTwiceIsStillOneAsk() {
        LocationWrites writes = new LocationWrites();
        assertEquals(LocationWrites.Written.FIRST, writes.write(LINES, A_VALUE));
        assertEquals(LocationWrites.Written.AGAIN, writes.write(LINES, A_VALUE));
    }

    @Test
    void locationsNeitherOfWhichHoldsTheOtherAreTwoWrites() {
        LocationWrites writes = new LocationWrites();
        assertEquals(LocationWrites.Written.FIRST, writes.write(AN_AMOUNT, A_VALUE));
        assertEquals(LocationWrites.Written.FIRST,
                writes.write(LINES.element().then("free"), ANOTHER));
        assertEquals(LocationWrites.Written.FIRST, writes.write(TermPath.of("k"), ANOTHER));
    }
}
