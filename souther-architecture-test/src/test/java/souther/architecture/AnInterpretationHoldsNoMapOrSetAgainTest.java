package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.FieldModel;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@link souther.compiler.partition.Interpretation} does not hold a {@code java.util.Map} or a
 * {@code java.util.Set} again.
 *
 * <p>{@code pins} is a {@link souther.compiler.carrier.Lookup}, which answers what a key is bound
 * to and offers no {@code keySet}, {@code entrySet} or {@code forEach} to take an order off. A
 * {@code Map} offers all three, and a {@code Map} built by copying one salts the order those hand
 * back — differently on some runs than on others — so every reader of {@code pins} has to consult
 * it by key, which is all a {@code Lookup} lets a reader do.
 *
 * <p><b>A field and not a census.</b> Once {@code pins} is a {@code Lookup}, nothing here needs to
 * watch its readers any more — a reader that reached for {@code keySet} or {@code forEach} does not
 * compile against one, so the type itself is what stops that reader from being written. What a type
 * cannot stop is the declaration going back the other way: nothing keeps a future edit from giving
 * {@code pins} a {@code Map} type again, and that edit would compile. So this reads the field back
 * and refuses it if it does.
 *
 * <p><b>One carrier and not a list of them.</b> A set of classes this holds itself to, added to by
 * hand as more are moved, is the same defect one level up — a class moved and never added is a class
 * this stops watching without saying so. So this is about {@link souther.compiler.partition
 * .Interpretation} alone, the way a rule about a form's own coefficients is about {@code
 * CanonicalForm} alone ({@link AFormIsWalkedThroughTheOrderItsPositionsDecideTest}); the next
 * carrier this repository moves gets a test of its own next to this one, not an entry added here.
 *
 * <p><b>Asked of the type and not of a list of names.</b> A field typed through the {@code Map} or
 * {@code Set} interface is not the only way this defect returns — a field typed as a platform
 * implementation this does not name by hand, such as {@code ConcurrentHashMap}, or a custom class
 * that implements either, holds exactly the same salted order. So what is asked is whether the
 * field's own type is a kind of {@code Map} or {@code Set}, read from the class itself, rather than
 * matched against a list of the ones this happened to think of.
 */
class AnInterpretationHoldsNoMapOrSetAgainTest {

    private static final String THE_CARRIER = "souther/compiler/partition/Interpretation";

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final CompiledOutputs AND_WHAT_IS_COMPILED_BESIDE_IT =
            CompiledOutputs.ofEverythingCompiledHere();

    @Test
    void noFieldOfInterpretationIsAMapOrASet() {
        assertEquals(List.of(), mapOrSetFieldsOf(COMPILED.read(THE_CARRIER)),
                THE_CARRIER + " was moved off java.util.Map/Set — a field reading as one of those"
                        + " again is the same defect the move closed, and the walk a reader could"
                        + " take off it would be salted the same way");
    }

    /**
     * And a class that does hold one is one this finds.
     *
     * <p>The positive control, and the reason there is a subject beside this test. Asked only of
     * what was compiled beside the test, not of what this repository publishes — which is exactly
     * what the rule above says holds none of these. Two fields: one typed through the {@code Map}
     * interface and one typed as a platform implementation this does not name by hand, so that
     * catching the second is not an accident of the first.
     */
    @Test
    void andAClassThatDoesHoldOneIsFound() {
        List<String> found = mapOrSetFieldsOf(AND_WHAT_IS_COMPILED_BESIDE_IT.read(THE_SUBJECT));

        assertTrue(found.contains(THE_SUBJECT + "#throughTheInterface Ljava/util/Map;"),
                "a field typed through java.util.Map was not found: " + found);
        assertTrue(found.contains(THE_SUBJECT
                        + "#throughAnImplementation Ljava/util/concurrent/ConcurrentHashMap;"),
                "a field typed as a platform implementation this rule does not name by hand was"
                        + " not found, so what it looks for is a name on a list rather than what"
                        + " the field's type is: " + found);
    }

    private static final String THE_SUBJECT =
            "souther/architecture/AnInterpretationHoldsNoMapOrSetAgainTest$AClassStillCarryingAMap";

    /** Every field of {@code model} whose declared type is a kind of {@code Map} or {@code Set}. */
    private static List<String> mapOrSetFieldsOf(ClassModel model) {
        List<String> found = new ArrayList<>();
        for (FieldModel field : model.fields()) {
            String descriptor = field.fieldTypeSymbol().descriptorString();
            if (descriptor.startsWith("L") && descriptor.endsWith(";")
                    && isAMapOrASet(descriptor.substring(1, descriptor.length() - 1))) {
                found.add(model.thisClass().name().stringValue() + "#"
                        + field.fieldName().stringValue() + " " + descriptor);
            }
        }
        return found;
    }

    /** Whether the type {@code internalName} names is a kind of {@code java.util.Map} or
     *  {@code java.util.Set}, answered by loading the class rather than by a list of names —
     *  every platform implementation and every custom one alike. */
    private static boolean isAMapOrASet(String internalName) {
        try {
            Class<?> loaded = Class.forName(internalName.replace('/', '.'), false,
                    AnInterpretationHoldsNoMapOrSetAgainTest.class.getClassLoader());
            return Map.class.isAssignableFrom(loaded) || Set.class.isAssignableFrom(loaded);
        } catch (ClassNotFoundException | LinkageError unreachable) {
            // A type nothing here can load answers this the way anything unproven does: no.
            return false;
        }
    }

    /**
     * A class written to still carry a {@code Map}, for the positive control above.
     *
     * <p>Nothing calls this and nothing may: what it is for is that the rule above has something to
     * find where a regression would look exactly like it.
     */
    static final class AClassStillCarryingAMap {

        private final Map<String, Integer> throughTheInterface = Map.of();

        private final ConcurrentHashMap<String, Integer> throughAnImplementation =
                new ConcurrentHashMap<>();

        private AClassStillCarryingAMap() {
        }
    }
}
