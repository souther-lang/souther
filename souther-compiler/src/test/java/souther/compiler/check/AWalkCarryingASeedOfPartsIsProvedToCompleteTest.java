package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.abort.GetsPast;
import souther.compiler.types.ValueName;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A library operation whose body is one walk carrying a count beside what it builds, and putting at
 * most one element into each collection a step, answers whatever it is handed apart from the
 * closures it applies. How the step names the collection it puts into is no part of that: a step
 * binding the grown collection to a name before returning it builds the same.
 */
class AWalkCarryingASeedOfPartsIsProvedToCompleteTest {

    private static void completes(String owner, String name) {
        ValueName.Stdlib.Operation operation = ValueName.Stdlib.operation(owner, name);
        assertInstanceOf(GetsPast.Always.class,
                LibraryEndings.shipped().completionApartFromWhatItIsHanded(operation),
                () -> operation.qualified() + " answers whatever it is handed");
    }

    @Test
    void aCounterBesideTheCollectionBuiltIsProved() {
        completes("List", "mapIndexed");
        completes("List", "take");
        completes("List", "drop");
        completes("List", "partition");
    }

    @Test
    void twoCollectionsBuiltAtOnceAreProved() {
        completes("List", "unzip");
    }
}
