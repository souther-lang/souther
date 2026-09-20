package souther.architecture;

import org.junit.jupiter.api.Test;
import souther.compiler.carrier.Lookup;

import java.lang.classfile.ClassModel;
import java.lang.classfile.FieldModel;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A class that holds a {@link souther.compiler.carrier.Lookup}, a
 * {@link souther.compiler.carrier.Membership} or an {@link souther.compiler.observe.ElementsTaken}
 * holds no {@code java.util.Map} or {@code java.util.Set} beside it.
 *
 * <p>Those three answer what a key is bound to, whether an element is in, and which element was
 * taken at each step — and none of them offers a walk to take an order off. A class holding one of
 * them has said which of its questions are of that kind, and a raw {@code Map} or {@code Set} in the
 * same class is a walk a reader can take off a copy whose order was salted, differently on some runs
 * than on others. Nothing stops a future edit adding one, and that edit would compile; so the fields
 * are read back and the class refused ({@link MapOrSetFields}).
 *
 * <p><b>The population is what the classes declare.</b> A class is in it by having a field of one of
 * those types, so a carrier moved onto one of them is covered by moving it and there is no list to
 * add it to. A class that moves back off them leaves the population and is covered by nothing; that
 * is the one direction this does not see, and the types are what a reader would notice missing.
 *
 * <p>Transitional: once every carrier of a package is moved, the population becomes every field the
 * package declares, and a rule built that way replaces this one.
 */
class EveryCarrierBuiltOnTheOrderFreeTypesHoldsNoMapOrSetTest {

    /** What a carrier holds instead of a map or a set, as a field descriptor names it. */
    private static final Set<String> ORDER_FREE_TYPES = Set.of(
            "Lsouther/compiler/carrier/Lookup;",
            "Lsouther/compiler/carrier/Membership;",
            "Lsouther/compiler/observe/ElementsTaken;");

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final CompiledOutputs AND_WHAT_IS_COMPILED_BESIDE_IT =
            CompiledOutputs.ofEverythingCompiledHere();

    @Test
    void noCarrierOfTheOrderFreeTypesHoldsAMapOrASet() {
        List<String> found = new ArrayList<>();
        for (ClassModel each : carriersIn(COMPILED)) {
            found.addAll(MapOrSetFields.in(each));
        }

        assertEquals(List.of(), found,
                "a class that holds a Lookup, a Membership or an ElementsTaken holds a Map or a Set"
                        + " beside it, and a reader can take a walk off that one whose order was"
                        + " salted by a copy");
    }

    /**
     * And the rule was asked of classes that were read.
     *
     * <p>A population found empty would be every carrier being clean, which is what a rule that had
     * stopped looking would read as.
     */
    @Test
    void andThereAreCarriersOfThemToAsk() {
        assertFalse(carriersIn(COMPILED).isEmpty(),
                "nothing this repository publishes holds one of the types this is about");
    }

    /**
     * And a class that holds one of them and a map beside it is found, and one holding only it is
     * not.
     *
     * <p>The controls for the population itself. {@link MapOrSetFields} has its own for what counts
     * as a map or a set; this is about which classes are asked.
     */
    @Test
    void andACarrierWithAMapBesideItIsFoundAndOneWithoutIsNot() {
        List<String> beside = carriersIn(AND_WHAT_IS_COMPILED_BESIDE_IT).stream()
                .map(each -> each.thisClass().name().stringValue()).toList();

        assertTrue(beside.contains(WITH_A_MAP),
                "a class holding a Lookup and a Map was not taken as a carrier: " + beside);
        assertTrue(beside.contains(WITHOUT),
                "a class holding only a Lookup was not taken as a carrier: " + beside);
        assertFalse(MapOrSetFields.in(AND_WHAT_IS_COMPILED_BESIDE_IT.read(WITH_A_MAP)).isEmpty(),
                "the map beside the Lookup was not found");
        assertTrue(MapOrSetFields.in(AND_WHAT_IS_COMPILED_BESIDE_IT.read(WITHOUT)).isEmpty());
    }

    private static final String WITH_A_MAP =
            "souther/architecture/EveryCarrierBuiltOnTheOrderFreeTypesHoldsNoMapOrSetTest"
                    + "$ACarrierWithAMapBesideIt";

    private static final String WITHOUT =
            "souther/architecture/EveryCarrierBuiltOnTheOrderFreeTypesHoldsNoMapOrSetTest"
                    + "$ACarrierWithNothingBesideIt";

    /** Every class of {@code where} with a field of one of the types this is about. */
    private static List<ClassModel> carriersIn(CompiledOutputs where) {
        List<ClassModel> carriers = new ArrayList<>();
        for (ClassModel each : where.all()) {
            for (FieldModel field : each.fields()) {
                if (ORDER_FREE_TYPES.contains(field.fieldTypeSymbol().descriptorString())) {
                    carriers.add(each);
                    break;
                }
            }
        }
        return carriers;
    }

    /** A carrier holding a map beside its lookup, for the control above. Nothing calls it. */
    static final class ACarrierWithAMapBesideIt {

        /** Read by the rule above and by nothing here. */
        @SuppressWarnings("UnusedVariable")
        private final Lookup<String, Integer> lookup = Lookup.built(_ -> { });

        /** As above. */
        @SuppressWarnings("UnusedVariable")
        private final Map<String, Integer> map = Map.of();

        private ACarrierWithAMapBesideIt() {
        }
    }

    /** A carrier holding only a lookup, for the control above. Nothing calls it. */
    static final class ACarrierWithNothingBesideIt {

        /** Read by the rule above and by nothing here. */
        @SuppressWarnings("UnusedVariable")
        private final Lookup<String, Integer> lookup = Lookup.built(_ -> { });

        private ACarrierWithNothingBesideIt() {
        }
    }
}
