package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.FieldModel;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A carrier this repository has moved off {@code java.util.Map}/{@code Set} does not hold one again.
 *
 * <p>{@code Map.copyOf} and {@code Set.copyOf} salt the order a value is built in, so a reader that
 * later takes one off the copy is reading something the runtime made up rather than the order the
 * writer wrote — issue #1775. The fix for a value the class reaches is not to stop copying but to
 * stop the value being a {@code Map} or a {@code Set} at all: {@link souther.compiler.carrier.Lookup}
 * answers what a key is bound to and offers no walk to salt in the first place.
 *
 * <p><b>A field and not a census.</b> Once a carrier is retyped this way, nothing here needs to watch
 * its readers any more — a reader that reached for {@code keySet} or {@code forEach} does not compile
 * against a {@link souther.compiler.carrier.Lookup}, so the type itself is what stops that reader
 * from being written. What this still has to watch is the one place a type does not reach: the
 * declaration. Nothing stops a future edit from giving {@link #MIGRATED} a field or a record
 * component typed {@code Map} or {@code Set} again, and that edit would compile — so this reads the
 * declaration back and refuses it if it does.
 *
 * <p><b>Named rather than swept.</b> Which carriers have been moved is a fact about work done one
 * class at a time and not one this can derive from the compiled output — a class that still holds a
 * {@code Map} may be a carrier nobody has read yet rather than a regression. So {@link #MIGRATED}
 * names the classes this repository has moved, and grows by one every time another does; nothing
 * shrinks it, because the direction a class leaves it in is always the wrong one.
 */
class AMigratedCarrierDoesNotBecomeAMapOrASetAgainTest {

    /** Every class whose fields this repository has moved off {@code Map}/{@code Set}, named as the
     *  work happens — one class at a time, growing as each root of issue #1775 is disposed of. */
    private static final Set<String> MIGRATED = Set.of(
            "souther/compiler/partition/Interpretation");

    /** The family a field must not be a kind of: {@code Map} and {@code Set} and what implements
     *  either in the platform. Not the interfaces alone — a field typed {@code HashMap} or
     *  {@code LinkedHashSet} is exactly as salted or as order-blind as one typed through the
     *  interface, and a rule that only read the interface would miss the field written the other
     *  way. */
    private static final Set<String> MAP_AND_SET_FAMILY = Set.of(
            "java/util/Map", "java/util/SequencedMap", "java/util/SortedMap",
            "java/util/NavigableMap", "java/util/HashMap", "java/util/LinkedHashMap",
            "java/util/TreeMap", "java/util/EnumMap", "java/util/IdentityHashMap",
            "java/util/WeakHashMap", "java/util/Set", "java/util/SequencedSet",
            "java/util/SortedSet", "java/util/NavigableSet", "java/util/HashSet",
            "java/util/LinkedHashSet", "java/util/TreeSet", "java/util/EnumSet");

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final CompiledOutputs AND_WHAT_IS_COMPILED_BESIDE_IT =
            CompiledOutputs.ofEverythingCompiledHere();

    @Test
    void noFieldOfAMigratedCarrierIsAMapOrASet() {
        for (String owner : MIGRATED) {
            List<String> found = mapOrSetFieldsOf(COMPILED.read(owner));
            assertEquals(List.of(), found,
                    owner + " was moved off java.util.Map/Set; a field reading as one of those"
                            + " again is the same defect the move closed, and the walk a reader"
                            + " could take off it would be salted the same way");
        }
    }

    /**
     * And the population this is about was actually read.
     *
     * <p>An owner {@link CompiledOutputs#read} cannot find fails the reading it is asked for rather
     * than answering about nothing, so a class named here that this repository stopped building
     * would already refuse the run above. This asks the narrower thing: that {@link #MIGRATED} is
     * not empty, which is the one way the rule above could pass while reading no class at all.
     */
    @Test
    void thePopulationNamedIsNotEmpty() {
        assertFalse(MIGRATED.isEmpty(),
                "nothing is named as migrated, so the rule above would pass while checking nothing");
    }

    /**
     * And a class that does hold one is one this finds.
     *
     * <p>The positive control, and the reason there is a subject beside this test. Asked only of
     * what was compiled beside the test — not of what this repository publishes, which is exactly
     * what the rule above says holds none of these — so a rule that had stopped reading fields at
     * all would still fail this one.
     */
    @Test
    void andAClassThatDoesHoldOneIsFound() {
        List<String> found =
                mapOrSetFieldsOf(AND_WHAT_IS_COMPILED_BESIDE_IT.read(THE_SUBJECT));

        assertTrue(found.contains(THE_SUBJECT + "#at Ljava/util/Map;"),
                "a subject written here with a field typed java.util.Map was not found: " + found);
    }

    private static final String THE_SUBJECT =
            "souther/architecture/AMigratedCarrierDoesNotBecomeAMapOrASetAgainTest$"
                    + "AClassStillCarryingAMap";

    /** Every field of {@code model} whose declared type is a kind of {@link #MAP_AND_SET_FAMILY}. */
    private static List<String> mapOrSetFieldsOf(ClassModel model) {
        List<String> found = new ArrayList<>();
        for (FieldModel field : model.fields()) {
            String descriptor = field.fieldTypeSymbol().descriptorString();
            if (!descriptor.startsWith("L") || !descriptor.endsWith(";")) {
                continue;
            }
            String named = descriptor.substring(1, descriptor.length() - 1);
            if (MAP_AND_SET_FAMILY.contains(named)) {
                found.add(model.thisClass().name().stringValue() + "#" + field.fieldName()
                        .stringValue() + " " + descriptor);
            }
        }
        return found;
    }

    /**
     * A class written to still carry a {@code Map}, for the positive control above.
     *
     * <p>Nothing calls this and nothing may: what it is for is that the rule above has something to
     * find where a regression would look exactly like it.
     */
    static final class AClassStillCarryingAMap {

        private final java.util.Map<String, Integer> at = java.util.Map.of();

        private AClassStillCarryingAMap() {
        }
    }
}
