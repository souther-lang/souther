package souther.compiler.coverage;

import souther.compiler.observe.ArmObservation;
import souther.compiler.Emitted;
import org.junit.jupiter.api.Test;

import souther.compiler.generated.MemoryClassLoader;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.query.Output;

import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a run says about the comparisons it evaluated.
 *
 * <p>Three states and not two. A comparison this plan numbers can have come out one way,
 * come out the other, or not have been reached at all — and a condition stops as soon as it is
 * settled, so the third happens whenever an earlier operand decides the answer.
 *
 * <p>The model is one {@code guard} over a conjunction, which is what makes this about the
 * comparisons rather than about the arms. Two of the three inputs take the same way out of the fork:
 * a reading that worked out which way a comparison went from the arm below it would give those two
 * the same answer, and they did different things.
 */
class AComparisonSaysWhichWayItCameOutTest {

    private static final String MODEL = """
            module example.trip

            data Submitted = { cost: Int }
            data Waiting = { cost: Int }

            behavior submit : (cost: Int) -> Submitted | Waiting
                constructs Submitted, Waiting

            let submit (cost) = {
                guard cost >= 0 && cost <= 100 else Waiting { cost = 0 }
                Submitted { cost = cost }
            }
            """;

    /**
     * The two ways of failing one conjunction are told apart, and the arms cannot tell them apart.
     *
     * <p>{@code -1} settles the condition at the first comparison and never reaches the second;
     * {@code 500} answers both. Both leave through the same arm, so the arms they lit are the same
     * set — and what the run recorded about the comparisons is not.
     */
    @Test
    void twoWaysOfFailingOneConditionAreNotOneObservation() {
        Compilation compilation = compiled();
        CoverageSites.Plan plan = checkedPlanOf(compilation);
        Behavior submit = new Behavior(probed(compilation), plan.identity());

        Observation early = submit.observing(-1L);
        Observation late = submit.observing(500L);

        assertEquals(armsOf(early, plan), armsOf(late, plan),
                "both rows leave through the same arm, which is why the arm cannot say this");
        assertNotEquals(early.comparisons(), late.comparisons(),
                "and the comparisons they answered are not the same");
    }

    /**
     * A comparison an operand short-circuited past is absent, rather than recorded as having failed.
     *
     * <p>The half of the vocabulary that a set of sites cannot hold. Absent and false are different
     * facts about a row — one says the row never got there, the other that it got there and went the
     * other way — and a claim about a comparison is answerable only where the two are apart.
     */
    @Test
    void aComparisonNeverReachedIsAbsentAndNotFalse() {
        Compilation compilation = compiled();
        Behavior submit = new Behavior(probed(compilation),
                checkedPlanOf(compilation).identity());

        Observation early = submit.observing(-1L);

        assertEquals(1, early.comparisons().size(),
                "the condition settled at the first comparison, so one comparison answered");
        ComparisonOutcome first = early.comparisons().iterator().next();
        assertFalse(first.held(), "and it answered by failing");

        Observation late = submit.observing(500L);
        ComparisonOutcome second = late.comparisons().stream()
                .filter(each -> each.at() != first.at())
                .findFirst()
                .orElseThrow(() -> new AssertionError(
                        "the row that answered both comparisons reached the second one"));
        assertFalse(early.taken().contains(second.at()),
                "which the row that short-circuited never reached");
        assertFalse(early.comparisons().contains(new ComparisonOutcome(second.at(), true)),
                "so it did not come out one way");
        assertFalse(early.comparisons().contains(new ComparisonOutcome(second.at(), false)),
                "nor the other");
    }

    /** Both ways out of one comparison are recorded, each of the row that took it. */
    @Test
    void aComparisonIsRecordedComingOutEitherWay() {
        Compilation compilation = compiled();
        Behavior submit = new Behavior(probed(compilation),
                checkedPlanOf(compilation).identity());

        Observation refused = submit.observing(500L);
        Observation accepted = submit.observing(50L);

        ComparisonOutcome failed = refused.comparisons().stream()
                .filter(each -> !each.held())
                .findFirst()
                .orElseThrow(() -> new AssertionError("the second comparison failed for this row"));
        assertTrue(accepted.comparisons().contains(new ComparisonOutcome(failed.at(), true)),
                "and the row inside the range answered the same comparison the other way");
        assertFalse(accepted.comparisons().contains(failed),
                "which is not the way this one came out");
    }

    /**
     * A comparison recorded as having come out a way is a comparison recorded as reached.
     *
     * <p>Held by how the recording is written rather than by the emitter keeping to it: one call
     * records both. So a run that has the first without the second is one nothing produces, and
     * whoever reads the sites and whoever reads the ways out are reading one run.
     */
    @Test
    void awayOutImpliesItsComparisonWasReached() {
        Compilation compilation = compiled();
        Behavior submit = new Behavior(probed(compilation),
                checkedPlanOf(compilation).identity());

        for (long cost : new long[] {-1L, 50L, 500L}) {
            Observation seen = submit.observing(cost);
            for (ComparisonOutcome each : seen.comparisons()) {
                assertTrue(seen.taken().contains(each.at()),
                        "a way out of " + each.at() + " was recorded, so it was reached");
            }
        }
    }

    /** The sites of {@code seen} that are arms, which is what a branch measure counts. */
    private static Set<ArmProbe> armsOf(Observation seen, CoverageSites.Plan plan) {
        return plan.numbering().align(seen).arms();
    }

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        return compilation;
    }

    /** The numbering of the bodies the classes below were generated from, asked of the check the
     *  emitter reads too. Named apart from the plans this package's other tests build straight from
     *  bodies, which have no compile behind them at all. */
    private static CoverageSites.Plan checkedPlanOf(Compilation compilation) {
        Bodies.Elaborated checked = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().get(0))).value();
        assertNotNull(checked, "the model under test compiles");
        return checked.plan();
    }

    private static Map<String, ClassFileImage> probed(Compilation compilation) {
        souther.compiler.generated.EvaluationArtifact artifact = compilation.db()
                .ask(new Output.Evaluated(compilation.modules().get(0),
                        ArmObservation.RECORD)).value();
        assertNotNull(artifact, "the model under test compiles");
        return artifact.classes();
    }

    /** One set of generated classes, loaded and applied. */
    private static final class Behavior {

        private final Object instance;
        private final Method apply;
        private final NumberingIdentity under;

        Behavior(Map<String, ClassFileImage> classes, NumberingIdentity under) {
            this.under = under;
            assertNotNull(classes, "the model under test compiles");
            ClassLoader loader = new MemoryClassLoader(classes,
                    AComparisonSaysWhichWayItCameOutTest.class.getClassLoader());
            try {
                Class<?> impl = Emitted.behavior(loader, "example.trip", "submit");
                Constructor<?> ctor = impl.getDeclaredConstructor();
                ctor.setAccessible(true);
                this.instance = ctor.newInstance();
                this.apply = impl.getDeclaredMethod("apply", Object.class);
                this.apply.setAccessible(true);
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            }
        }

        /** What the classes recorded, as numbers under the numbering they were emitted with. */
        Observation observing(long cost) {
            Probe.begin(under);
            try {
                apply.invoke(instance, cost);
                return Probe.snapshot();
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            } finally {
                Probe.end();
            }
        }
    }
}
