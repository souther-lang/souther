package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.Attributes;
import java.lang.classfile.ClassModel;
import java.lang.classfile.attribute.PermittedSubclassesAttribute;
import java.lang.classfile.constantpool.ClassEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Every shape a coverage item's demand takes is asked whether the rules on the way to it leave it
 * anything.
 *
 * <p>The check itself is one switch over the shapes and the compiler holds it to all of them: a
 * shape added tomorrow does not compile until that switch says what its quantity is. What nothing
 * holds is the other half — whether anything states, of that shape, that a region refusing its
 * quantity is a proof. A shape whose arm returns a quantity nobody crosses with anything passes
 * every test there is, and what it carries is a contradiction with a finite proof walked for until a
 * figure of this compiler's runs out.
 *
 * <p>So the population is read off the sealed type rather than listed here, and what states the
 * property is read off its own constant pool. The two are separate from the property itself on
 * purpose: that one is about whether the answer is right, and this one is about whether the answer
 * was asked for. Held in one place, a shape nobody wrote a case for would leave the property green
 * over the shapes somebody did.
 */
class EveryShapeOfAStandingIsAskedWhetherTheRegionRefusesItTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofEverythingCompiledHere();

    /** What a coverage item asks of a row, which has one shape per kind of search. */
    private static final String STANDING = "souther/compiler/partition/Standing";

    /** What states that a region leaving the quantity nowhere is a proof. */
    private static final String STATES =
            "souther/compiler/partition/"
                    + "ARegionThatLeavesTheQuantityNowhereTheItemAsksIsAProofTest";

    /** Every shape is named by the test that states the property. */
    @Test
    void everyShapeIsAskedOfTheCheckByWhatStatesIt() {
        Set<String> shapes = shapesOfAStanding();
        Set<String> named = classesNamedBy(STATES);

        assertFalse(shapes.isEmpty(), "a sealed type with no shapes is a population this cannot"
                + " have read off the right class");
        Set<String> missing = new TreeSet<>(shapes);
        missing.removeAll(named);
        assertEquals(Set.of(), missing,
                () -> "these shapes of a coverage item's demand have nothing saying what a region"
                        + " that refuses their quantity comes to: " + missing);
    }

    /** The shapes, as the sealed type itself lists them. */
    private static Set<String> shapesOfAStanding() {
        ClassModel standing = COMPILED.read(STANDING);
        PermittedSubclassesAttribute permitted = standing
                .findAttribute(Attributes.permittedSubclasses())
                .orElseThrow(() -> new AssertionError(
                        STANDING + " is not sealed, so what a reader of it has to answer for is no"
                                + " longer a list this can read"));
        Set<String> shapes = new LinkedHashSet<>();
        permitted.permittedSubclasses().forEach(each -> shapes.add(each.asInternalName()));
        return shapes;
    }

    /** Every class a compiled class names, which is what it was written against. */
    private static Set<String> classesNamedBy(String internalName) {
        Set<String> named = new LinkedHashSet<>();
        for (PoolEntry entry : COMPILED.read(internalName).constantPool()) {
            if (entry instanceof ClassEntry each) {
                named.add(each.asInternalName());
            }
        }
        return named;
    }
}
