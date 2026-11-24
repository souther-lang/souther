package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ExpansionSite;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenOwner;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two choices of a comparison are put together only where they are one, and a call site the source
 * wrote expands one thing: asked to put two steps at one site that expand different things, the
 * order refuses and does not leave them tied.
 */
class TheChoicesOfAComparisonAreOrderedBySiteAndRefuseWhatASiteDoesNotDoTest {

    private static final WrittenOwner BODY = new WrittenOwner.Body("m", "f");

    private static SourceConstructOrigin construct(int ordinal, SourceConstruct kind) {
        return SourceConstructOrigin.written(BODY, ordinal, kind);
    }

    private static ExpansionLineage.Step step(String expanded, int call) {
        return new ExpansionLineage.Step(new ValueName.Helper("m", expanded),
                new ExpansionSite.Written(construct(call, SourceConstruct.CALL)));
    }

    private static WrittenChoice choice(int at, ExpansionLineage.Step... through) {
        return new WrittenChoice(construct(at, SourceConstruct.IF), List.of(through));
    }

    private static int compare(WrittenChoice one, WrittenChoice other) {
        return WrittenChoice.inASteadyOrder().compare(one, other);
    }

    @Test
    void theSameChoiceIsTheSameAndTwoConstructsAreTwo() {
        assertEquals(0, compare(choice(1, step("g", 3)), choice(1, step("g", 3))));
        int order = compare(choice(1), choice(2));
        assertTrue(order != 0, "two constructs are two choices");
        assertEquals(-Integer.signum(order), Integer.signum(compare(choice(2), choice(1))));
    }

    @Test
    void theSameConstructReachedThroughTwoSitesIsTwoChoices() {
        int order = compare(choice(1, step("g", 3)), choice(1, step("g", 4)));
        assertTrue(order != 0, "two sites are two choices");
        assertEquals(-Integer.signum(order),
                Integer.signum(compare(choice(1, step("g", 4)), choice(1, step("g", 3)))));
    }

    @Test
    void aChoiceReachedThroughACallFollowsTheOneReachedThroughNone() {
        assertTrue(compare(choice(1), choice(1, step("g", 3))) < 0);
    }

    @Test
    void oneSiteExpandingTwoThingsIsRefusedAndNotTied() {
        assertThrows(IllegalStateException.class,
                () -> compare(choice(1, step("g", 3)), choice(1, step("h", 3))));
    }
}
