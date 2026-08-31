package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.WhatWasCompiled;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What a rule calls a place is made where a name is read, and nowhere else.
 *
 * <p>A {@link RuleKey} is what one value's rules call somewhere in it. Two things make one: the walk
 * over a declaration, which follows the names as they are written, and the translation from a
 * position to the name a rule of the value at some root would write for it. Anything else making
 * one is a third way of deciding which steps of a place are names a clause can write — which is the
 * question the type exists to have one answer to, since a step into a sequence and a narrowing to a
 * case are places a value can be and are not names any rule writes.
 *
 * <p>Read off what javac made of the module rather than off the source. A call is in the constant
 * pool however it was written, so a maker cannot get out of this by writing the call somewhere
 * shorter or inside a lambda.
 *
 * <p>An entry added to this list is a finding and not a formality: it says somewhere new decides
 * what a rule may name, and whether it wanted to decide that or wanted to be handed the answer is
 * the thing to settle before the list is edited.
 */
class ANameARuleWritesIsMadeWhereOneIsReadTest {

    /**
     * Who makes one, in three groups.
     *
     * <p>The walk over a declaration's own names, which is where a reading writes them down as it
     * follows them ({@code GuaranteeWalk}, {@code InvariantChecker}); the translation from a place
     * to what a rule calls it ({@code TermPath}); and the readers that lift a field a declaration
     * writes to the name its own rules give it, which is one step and no decision about which steps
     * are names.
     *
     * <p>{@code UniversalElementFacts} is in the first group and is the one to watch: it rebases
     * what a reading said about an element onto the field a construction wrote it at, which is the
     * one place a name is made out of another name.
     */
    private static final List<String> THE_MAKERS = List.of(
            "souther.compiler.check.CardinalityTransfer",
            "souther.compiler.check.GuaranteeWalk",
            "souther.compiler.check.InvariantChecker",
            "souther.compiler.check.TypeCardinality",
            "souther.compiler.check.UniversalElementFacts",
            "souther.compiler.inputs.TermPath",
            "souther.compiler.partition.Partitions");

    @Test
    void aNameIsMadeWhereNamesAreRead() {
        assertEquals(THE_MAKERS, makersOfARuleKey(),
                "these decide what a rule may name, and this is who does");
    }

    /**
     * And the translation from a place to a name has one home.
     *
     * <p>The one thing that says which steps below a root are names a rule writes. A second would
     * be a second answer about a position inside a sequence or under a case, and those are exactly
     * the places where a name and a position part company.
     */
    @Test
    void aPlaceBecomesANameInOnePlace() {
        assertFalse(WhatWasCompiled.callersOf(souther.compiler.inputs.TermPath.class,
                        "ruleKeyUnder").isEmpty(),
                "a position is turned into a name somewhere, or this is watching a name nothing"
                        + " calls");
        assertEquals(List.of("souther.compiler.inputs.InputDomain",
                        "souther.compiler.inputs.PlacedRules",
                        "souther.compiler.inputs.ReadQuantities",
                        "souther.compiler.inputs.RuleAddress",
                        "souther.compiler.partition.Generator"),
                callersOf(souther.compiler.inputs.TermPath.class, "ruleKeyUnder"),
                "a position becomes what a rule calls it here, and is handed on as that");
    }

    /** Every class that builds a {@link RuleKey}, however it spells the making. */
    private static List<String> makersOfARuleKey() {
        Set<String> found = WhatWasCompiled.callersOf(RuleKey.class, "<init>");
        for (String each : List.of("of", "then", "readFrom")) {
            found.addAll(WhatWasCompiled.callersOf(RuleKey.class, each));
        }
        return found.stream().filter(each -> !each.equals(RuleKey.class.getName())).sorted()
                .toList();
    }

    /** Who calls {@code method} on {@code on}, leaving out the class that declares it. */
    private static List<String> callersOf(Class<?> on, String method) {
        return WhatWasCompiled.callersOf(on, method).stream()
                .filter(each -> !each.equals(on.getName())).sorted().toList();
    }
}
