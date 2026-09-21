package souther.compiler;

import souther.compiler.coverage.Numberings;
import souther.compiler.partition.ArmDisposition;
import souther.compiler.partition.Discharge;
import souther.compiler.partition.FillResult;
import souther.compiler.partition.GenerationPlan;
import souther.compiler.partition.Generator;
import souther.compiler.partition.ObligationIdentity;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAccount;
import souther.compiler.query.Compilation;
import souther.compiler.query.Composition;
import souther.compiler.query.OfferingRequest;
import souther.compiler.query.RowWork;
import souther.compiler.query.Settlements;
import souther.compiler.reading.PathAccess;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The account identity {@code Adequacy.RowsOwed} binds an arm's search target to is the one every
 * downstream reader of the generation plan sees, and a target it never bound one to is refused
 * rather than read as an arm this behavior has none of.
 *
 * <p>Not the {@code Bodies.Observable} versus {@code Bodies.Checked} disagreement issue #1831 was
 * triggered by. That is a fact about a different query (a module with one clean behavior beside a
 * declaration that does not check), and this correspondence no longer depends on which of the two
 * {@code Settlements} happens to read: {@code RowsOwed} binds the target and the identity together
 * once, and nothing downstream rebuilds the pairing from a second derivation of the body.
 */
class AnArmHandedToGenerationKeepsTheIdentityRowsOwedGaveItTest {

    private static final String MODEL = """
            module example.unreachedarm

            data Speed = Slow | Fast | Ludicrous
            data Fee = Int

            behavior feeFor : (speed: Speed) -> Fee
                constructs Fee

            let feeFor (speed) =
                match speed with
                    | Slow -> Fee(0)
                    | Fast -> Fee(10)
                    | Ludicrous -> Fee(20)

            example feeFor
                | (Slow) -> Fee(0)
                | (Fast) -> Fee(10)
            """;

    /**
     * Every arm in the plan a generation was handed is one {@code RowsOwed} bound an identity to,
     * and that same identity is what the offering requests it under.
     */
    @Test
    void everyArmInTheGenerationPlanIsOneRowsOwedBoundAnIdentityTo() {
        Compilation compilation = measured();

        RowWork owed = compilation.db().ask(new Adequacy.RowsOwed("example.unreachedarm", "feeFor"))
                .value();
        assertNotNull(owed, "the module measures a behavior with an unreached arm");
        assertFalse(owed.arms().isEmpty(), "the ludicrous arm is not reached by either example");

        Map<String, Adequacy.Filling> generated =
                Adequacy.generatedOf(compilation.db(), "example.unreachedarm");
        Adequacy.Filling filling = generated.get("feeFor");
        assertNotNull(filling, "a generation was made for the behavior");

        assertEquals(new LinkedHashSet<>(owed.arms().stream().map(RowWork.Arm::target).toList()),
                new LinkedHashSet<>(filling.composed().plan().armsOwed()),
                "every arm the generation was asked for is one RowsOwed bound to an identity, and"
                        + " none of that binding's arms is missing from what the plan holds");

        Settlements table = settlementsOf(compilation, generated);
        for (RowWork.Arm arm : owed.arms()) {
            ObligationIdentity.OfAnArm identity = arm.identity();
            assertTrue(table.requested().contains(identity),
                    () -> identity + " is requested under the identity RowsOwed bound to its"
                            + " search target: " + table.requested());
        }
    }

    /**
     * A target the generation plan holds and {@code RowsOwed} never bound an identity to is a
     * provenance failure, not an arm this behavior happens to have none of — {@code Settlements}
     * refuses rather than silently leaving it out of what it requests.
     *
     * <p>This is the defect #1831 traced to {@code arm != null}: a lookup miss read as absence
     * instead of as a broken correspondence.
     */
    @Test
    void anArmTheGenerationPlanHoldsWithNoBoundIdentityIsRefused() {
        Compilation compilation = measured();
        Map<String, Adequacy.Filling> generated =
                Adequacy.generatedOf(compilation.db(), "example.unreachedarm");
        Adequacy.Filling real = generated.get("feeFor");
        assertNotNull(real);

        // A target no numbering of this module ever handed out, so RowsOwed's binding for "feeFor"
        // has no entry for it whatever the module measures.
        Generator.ArmOwed phantom = new Generator.ArmOwed(Numberings.arm(1, 0));
        GenerationPlan tamperedPlan = GenerationPlan.of(real.composed().plan().subject(),
                List.of(), List.of(phantom), List.of(), List.of());
        FillResult tamperedFill = new FillResult(tamperedPlan, new LinkedHashMap<>(), List.of(),
                List.of(), new Discharge(Map.of(),
                        Map.of(phantom, new ArmDisposition.NoWayIn(
                                new PathAccess.Unsupported(
                                        PathAccess.Unsupported.Why.WAYS_NOT_ENUMERABLE))),
                        Map.of(), Map.of()));
        Adequacy.Filling tampered = new Adequacy.Filling(tamperedFill,
                Generator.GenerationResult.NONE, Adequacy.Generated.RowsForRules.NOTHING,
                List.of());

        Map<String, Adequacy.Filling> withTamperedPlan = new LinkedHashMap<>(generated);
        withTamperedPlan.put("feeFor", tampered);

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> settlementsOf(compilation, withTamperedPlan));
        assertTrue(refused.getMessage().contains("RowsOwed did not bind"), refused.getMessage());
    }

    private static Settlements settlementsOf(Compilation compilation,
                                             Map<String, Adequacy.Filling> generated) {
        OfferingRequest request = OfferingRequest.overTheModule("example.unreachedarm");
        BorderAccount account = Adequacy.accountFor(compilation.db(), request.module(),
                request.scope());
        Composition composed = Composition.composed(request, generated, account);
        return Settlements.of(compilation.db(), composed);
    }

    private static Compilation measured() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
