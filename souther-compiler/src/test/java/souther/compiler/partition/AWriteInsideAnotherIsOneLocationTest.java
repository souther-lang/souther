package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclaredBounds;
import souther.compiler.diag.Messages;
import souther.compiler.diag.msg.Message;
import souther.compiler.inputs.TermPath;

import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

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
 * do is compose a whole value and a value inside it into one write. And it comes back naming the two
 * places and what each was asked for, so a reader is not sent to look for one place asked two
 * values where one of the two was a count.
 */
class AWriteInsideAnotherIsOneLocationTest {

    private static final TermPath LINES = TermPath.of("lines");

    private static final TermPath AN_AMOUNT = LINES.element().then("amount");

    private static final TermPath HELD = LINES.element().then("parts");

    private static final List<FixtureTemplate> A_VALUE = List.of(FixtureTemplate.integer(1));

    private static final List<FixtureTemplate> ANOTHER = List.of(FixtureTemplate.integer(2));

    private static final DeclaredBounds.CountRange TWO = new DeclaredBounds.CountRange(2, 2);

    private static final DeclaredBounds.CountRange THREE = new DeclaredBounds.CountRange(3, 3);

    private static final LocationWrites.Written FIRST = new LocationWrites.Written.First();

    private static LocationWrites.Written.Ask value(TermPath at) {
        return LocationWrites.Written.Ask.aValue(at);
    }

    private static LocationWrites.Written.Ask howMany(TermPath at) {
        return LocationWrites.Written.Ask.howManyItHolds(at);
    }

    private static LocationWrites.Written.Conflicting conflict(LocationWrites.Written.Ask asked,
                                                               LocationWrites.Written.Ask already) {
        return new LocationWrites.Written.Conflicting(asked, already);
    }

    @Test
    void aValueInsideOneAlreadyWrittenConflicts() {
        LocationWrites writes = new LocationWrites();
        assertEquals(FIRST, writes.write(LINES, A_VALUE));
        assertEquals(conflict(value(AN_AMOUNT), value(LINES)), writes.write(AN_AMOUNT, ANOTHER),
                "the container was written whole, so a position inside it is the same value asked"
                        + " for a second time");
    }

    @Test
    void aValueAroundOneAlreadyWrittenConflicts() {
        LocationWrites writes = new LocationWrites();
        assertEquals(FIRST, writes.write(AN_AMOUNT, A_VALUE));
        assertEquals(conflict(value(LINES), value(AN_AMOUNT)), writes.write(LINES, ANOTHER),
                "and the order the two arrive in says nothing about whether they are one location");
    }

    @Test
    void aConflictOfOnePlaceInsideAnotherNamesBothWhicheverCameFirst() {
        String inside = "`lines[*].amount` is inside `lines`, and each is asked for a value of its"
                + " own";
        assertEquals(inside, english(conflict(value(AN_AMOUNT), value(LINES)).said()));
        assertEquals(inside, english(conflict(value(LINES), value(AN_AMOUNT)).said()));
        assertEquals("`lines` would have to hold two values at once",
                english(conflict(value(LINES), value(LINES)).said()));
    }

    @Test
    void theSameAskTwiceIsStillOneAsk() {
        LocationWrites writes = new LocationWrites();
        assertEquals(FIRST, writes.write(LINES, A_VALUE));
        assertEquals(new LocationWrites.Written.Again(), writes.write(LINES, A_VALUE));
    }

    @Test
    void anotherValueAtTheSamePlaceConflictsWithThatPlace() {
        LocationWrites writes = new LocationWrites();
        assertEquals(FIRST, writes.write(LINES, A_VALUE));
        assertEquals(conflict(value(LINES), value(LINES)), writes.write(LINES, ANOTHER));
    }

    @Test
    void locationsNeitherOfWhichHoldsTheOtherAreTwoWrites() {
        LocationWrites writes = new LocationWrites();
        assertEquals(FIRST, writes.write(AN_AMOUNT, A_VALUE));
        assertEquals(FIRST, writes.write(LINES.element().then("free"), ANOTHER));
        assertEquals(FIRST, writes.write(TermPath.of("k"), ANOTHER));
    }

    /**
     * Two counts asked of one container are said as two counts, and never as two values: the
     * container was asked to hold so many twice, and no number is both.
     */
    @Test
    void twoCountsOfOneContainerAreSaidAsCounts() {
        LocationWrites writes = new LocationWrites();
        assertEquals(FIRST, writes.size(LINES, TWO));
        LocationWrites.Written refused = writes.size(LINES, THREE);
        assertEquals(conflict(howMany(LINES), howMany(LINES)), refused);
        assertEquals("`lines` is asked to hold two numbers of elements, and no number is both",
                english(((LocationWrites.Written.Conflicting) refused).said()));
    }

    /**
     * A value and a count at one location are said as that, whichever came first: the value says
     * how many the container holds.
     */
    @Test
    void aValueAndACountOfOneContainerAreSaidAsAValueAndACount() {
        LocationWrites countedFirst = new LocationWrites();
        assertEquals(FIRST, countedFirst.size(LINES, TWO));
        LocationWrites.Written written = countedFirst.write(LINES, A_VALUE);
        LocationWrites valuedFirst = new LocationWrites();
        assertEquals(FIRST, valuedFirst.write(LINES, A_VALUE));
        LocationWrites.Written sized = valuedFirst.size(LINES, TWO);
        assertEquals(conflict(value(LINES), howMany(LINES)), written);
        assertEquals(conflict(howMany(LINES), value(LINES)), sized);
        String said = "`lines` is asked for a value and for how many elements it holds, and the"
                + " value already says how many";
        assertEquals(said, english(((LocationWrites.Written.Conflicting) written).said()));
        assertEquals(said, english(((LocationWrites.Written.Conflicting) sized).said()));
    }

    /** A count of a container inside a value written whole names both and what each was asked. */
    @Test
    void aCountInsideAValueIsSaidAsACountInsideAValue() {
        LocationWrites writes = new LocationWrites();
        assertEquals(FIRST, writes.write(LINES, A_VALUE));
        LocationWrites.Written refused = writes.size(HELD, TWO);
        assertEquals(conflict(howMany(HELD), value(LINES)), refused);
        assertEquals("`lines[*].parts` is inside `lines`, and the value asked at `lines` already"
                        + " says how many elements `lines[*].parts` holds",
                english(((LocationWrites.Written.Conflicting) refused).said()));
    }

    /** What a conflict says, in the words an English reader is shown. */
    private static String english(Message said) {
        return Messages.render(said, Locale.ENGLISH);
    }

    /** What a row can be written to hold is no conflict, and is not made one. */
    @Test
    void aPairARowCanHoldIsNoConflict() {
        LocationWrites writes = new LocationWrites();
        assertEquals(FIRST, writes.size(LINES, TWO));
        assertEquals(FIRST, writes.write(AN_AMOUNT, A_VALUE),
                "a value inside a container asked to hold so many is one more thing it holds");
        assertThrows(IllegalArgumentException.class,
                () -> conflict(value(AN_AMOUNT), howMany(LINES)));
        assertThrows(IllegalArgumentException.class,
                () -> conflict(howMany(HELD), howMany(LINES)));
        assertThrows(IllegalArgumentException.class,
                () -> conflict(value(TermPath.of("k")), value(LINES)));
    }
}
