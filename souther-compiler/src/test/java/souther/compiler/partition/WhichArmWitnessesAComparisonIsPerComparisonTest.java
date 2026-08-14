package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeChecker;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Which arm proves a comparison ran is asked of the comparison, not of the condition it sits in.
 *
 * <p>A condition that is nothing but {@code &&} settles it for every operand at once, and so does one
 * that is nothing but {@code ||}. A condition made of both does not: in {@code A && (B || C)},
 * reaching the arm where the whole thing held proves {@code A} was true, and so proves {@code B} was
 * evaluated — while {@code C} ran only where {@code B} was false, which neither arm separates.
 *
 * <p>Answering per condition rather than per comparison gets {@code B} wrong in the direction that
 * costs an author work: an edge reported as one no arm witnesses is one nothing will ever be shown
 * to have reached, and here the {@code then} arm shows it.
 */
class WhichArmWitnessesAComparisonIsPerComparisonTest {

    private static Map<String, OriginRef.GuardOrigin.Witness> witnesses(String condition) {
        String source = """
                module example.nested

                data Request = { a: Int, b: Int, c: Int }

                data Low
                data High

                behavior pick : (r: Request) -> Low | High
                    constructs Low, High

                let pick (r) =
                    if CONDITION
                        then High
                        else Low
                """.replace("CONDITION", condition);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Symbols symbols = compilation.db().ask(new Shapes.Scope(module)).value();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, () -> "the model under test compiles: " + condition);
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals("pick")).findFirst().orElseThrow();
        Core body = checked.behaviorBodies().get("pick");
        CoverageSites.Plan plan = CoverageSites.of("m.sou", checked.behaviorBodies());
        GuardThresholds.Guards guards = GuardThresholds.of("pick", body, plan,
                spec.params().stream().map(Hir.Param::name).toList(), symbols);
        Map<String, OriginRef.GuardOrigin.Witness> out = new LinkedHashMap<>();
        for (Threshold each : guards.thresholds()) {
            out.put(each.path().toString(), each.origin().witness());
        }
        return out;
    }

    /** A conjunction: the first is proved by either arm, the rest by the arm it held on. */
    @Test
    void aConjunctionLeavesTheRestToTheArmItHeldOn() {
        assertEquals(Map.of("r.a", OriginRef.GuardOrigin.Witness.BOTH,
                        "r.b", OriginRef.GuardOrigin.Witness.THEN),
                witnesses("r.a >= 0 && r.b >= 0"));
    }

    /** A disjunction: the arm it did not hold on. */
    @Test
    void aDisjunctionLeavesTheRestToTheOtherArm() {
        assertEquals(Map.of("r.a", OriginRef.GuardOrigin.Witness.BOTH,
                        "r.b", OriginRef.GuardOrigin.Witness.ELSE),
                witnesses("r.a >= 0 || r.b >= 0"));
    }

    /**
     * A conjunction over a disjunction. The disjunction runs whenever the conjunction held, so its
     * first operand does too; its second ran only where the first did not.
     */
    @Test
    void aDisjunctionInsideAConjunctionKeepsWhatItsPlaceProves() {
        assertEquals(Map.of("r.a", OriginRef.GuardOrigin.Witness.BOTH,
                        "r.b", OriginRef.GuardOrigin.Witness.THEN,
                        "r.c", OriginRef.GuardOrigin.Witness.NEITHER),
                witnesses("r.a >= 0 && (r.b >= 0 || r.c >= 0)"));
    }

    /** And a disjunction under a conjunction leaves its own second operand to neither arm. */
    @Test
    void aConjunctionOverADisjunctionKeepsWhatItsPlaceProves() {
        assertEquals(Map.of("r.a", OriginRef.GuardOrigin.Witness.BOTH,
                        "r.b", OriginRef.GuardOrigin.Witness.NEITHER,
                        "r.c", OriginRef.GuardOrigin.Witness.THEN),
                witnesses("(r.a >= 0 || r.b >= 0) && r.c >= 0"));
    }

    /**
     * A conjunction inside a disjunction, which is the other nesting.
     *
     * <p>{@code B} is reached whenever {@code A} was false, and reaching the arm where the whole
     * thing failed is what says so. {@code C} is not: the conjunction failing is as easily
     * {@code B} being false as {@code C} being, and then {@code C} never ran — on either arm.
     */
    @Test
    void aConjunctionInsideADisjunctionKeepsWhatItsPlaceProves() {
        assertEquals(Map.of("r.a", OriginRef.GuardOrigin.Witness.BOTH,
                        "r.b", OriginRef.GuardOrigin.Witness.ELSE,
                        "r.c", OriginRef.GuardOrigin.Witness.NEITHER),
                witnesses("r.a >= 0 || (r.b >= 0 && r.c >= 0)"));
    }

    /** And a conjunction over a disjunction, where the last operand is the one the failure reaches. */
    @Test
    void aDisjunctionOverAConjunctionKeepsWhatItsPlaceProves() {
        assertEquals(Map.of("r.a", OriginRef.GuardOrigin.Witness.BOTH,
                        "r.b", OriginRef.GuardOrigin.Witness.NEITHER,
                        "r.c", OriginRef.GuardOrigin.Witness.ELSE),
                witnesses("(r.a >= 0 && r.b >= 0) || r.c >= 0"));
    }
}
