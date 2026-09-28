package souther.program.api;

import souther.compiler.program.CheckedBehavior;
import souther.compiler.program.CheckedProgram;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * {@link CheckedBehavior#requirements} reaches a program's reader from the same
 * {@code depends on} the checker already resolved (spec §depends-on,
 * §composition-with-requirements) — projected, not walked a second time here or by whatever asks
 * for it.
 */
class ACheckedBehaviorsRequirementsReachFromTheDependsOnItWroteTest {

    private static final String SRC = """
            module demo

            data MemberId = String
            data Found = { id: MemberId }
            data Missing = { why: String }

            behavior findMember : (id: MemberId) -> Found | Missing

            behavior logLookup : (id: MemberId) -> Found | Missing

            behavior place : (id: MemberId, other: MemberId) -> Found | Missing
                depends on findMember, logLookup

            let place (id, other, findMember, logLookup) = match findMember(id) with
                | Found   -> logLookup(other)
                | Missing -> findMember(other)
            """;

    @Test
    void aRequirementReachesTheCheckedBehaviorInTheOrderItWasWritten() {
        CheckedProgram program = CheckedProgram.of(List.of(SRC));

        CheckedBehavior place = program.module("demo").behavior(new ValueName.Behavior("demo",
                "place"));

        assertEquals(List.of(new ValueName.Behavior("demo", "findMember"),
                new ValueName.Behavior("demo", "logLookup")), place.requirements(),
                "a construction requires what its depends on names, in the order it named them —"
                        + " the order an injecting constructor takes them in");
    }

    @Test
    void aBehaviorWithNoDependsOnRequiresNothing() {
        CheckedProgram program = CheckedProgram.of(List.of(SRC));

        CheckedBehavior findMember = program.module("demo").behavior(
                new ValueName.Behavior("demo", "findMember"));

        assertEquals(List.of(), findMember.requirements(),
                "an injection target requires nothing to construct: the Java side supplies it");
    }
}
