package souther.compiler.reading;

import souther.compiler.observe.ArmObservation;
import souther.compiler.Emitted;
import org.junit.jupiter.api.Test;

import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.Observation;
import souther.compiler.coverage.Probe;
import souther.compiler.generated.MemoryClassLoader;
import souther.compiler.inputs.InputDomain;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.query.Scopes;

import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a group says about a run, held against a run.
 *
 * <p>A group is read off the body: these decisions are consumed into one value, and each of them can
 * be settled these ways. Everything downstream acts on that reading — a row is composed to settle
 * each factor one way and is then offered, and named, for the combination. Until the reading can be
 * held to something, every step of it is a statement nothing can be found to disagree with, which is
 * how four separate misreadings of it came to look alike.
 *
 * <p>So each way of settling a decision carries what a run that settled it would be seen to have
 * done. This drives the behavior at each of the four combinations of a model with two decisions and
 * asks the run: for every row, exactly one way of settling each factor is one the run did, and the
 * four rows did four different things. A reading that named the wrong place, or named a place under
 * a condition no row can be steered into, does not come out that way.
 */
class AClaimIsWhatARunThatSettledItWouldBeSeenToDoTest {

    /** Two decisions consumed into one value, one per input, so each row settles both. */
    private static final String FEE = """
            module example.charge

            data Fee = Int
                invariant value >= 0

            behavior chargeFor : (spend: Int, bonus: Int) -> Fee
                constructs Fee

            let chargeFor (spend, bonus) =
                Fee((if spend > 100 then 10 else 20) + (if bonus > 5 then 1 else 2))
            """;

    /**
     * What the run did is what the reading said settling the factor that way takes.
     *
     * <p>Three things held against each other and not two. Each way of settling a factor says what
     * it takes of an input — this position, this side of this comparison — and what a run that did
     * it would be seen to have done. The rows below are chosen so that the first is known from the
     * source: at {@code (500, 50)} the model's two comparisons come out true and true, and so on
     * round the four.
     *
     * <p>So the way the run is seen to have settled each factor is looked up, and what that way says
     * about the inputs is read back out and held against what the row actually was. A claim naming
     * the wrong place, the wrong side of the right place, or a place the row cannot be steered into
     * comes apart here — the first two by disagreeing with the row, the last by no way of settling
     * the factor holding at all.
     */
    @Test
    void whatARunIsSeenToDoIsWhatTheWayItSettledTheFactorTakes() {
        Model model = Model.of(FEE, "chargeFor");
        List<Interaction> found = model.groups();
        assertEquals(1, found.size(), "the two decisions meet once: " + found);
        Interaction group = found.get(0);
        assertEquals(2, group.factors().size(), "one factor per decision: " + group);

        for (long spend : new long[] {500L, 5L}) {
            for (long bonus : new long[] {50L, 1L}) {
                assertEquals(Map.of("spend", spend > 100, "bonus", bonus > 5),
                        takenBy(group, model.observing(spend, bonus)),
                        "the row (" + spend + ", " + bonus + ") was seen settling the factors the "
                                + "way the model settles them for it");
            }
        }
    }

    /**
     * The way in is what a run has to have done as well.
     *
     * <p>Empty here, this meeting standing in no arm. Asserted so that the half of a group that says
     * how to arrive is read at all: a group is a path to the meeting as much as the outcomes at it,
     * and a reading that dropped the path would be one nothing here would notice.
     */
    @Test
    void theWayInIsHeldToTheSameRun() {
        Model model = Model.of(FEE, "chargeFor");
        Interaction group = model.groups().get(0);

        Observation seen = model.observing(500L, 50L);
        assertEquals(List.of(), group.reachClaims().stream()
                        .filter(claim -> !claim.satisfiedBy(seen)).toList(),
                "a row that reaches the meeting did everything the way in names");
    }

    /**
     * Which side of which position each factor was seen settled at.
     *
     * <p>Exactly one way per factor, in both directions. Two of them holding of one run would say
     * they are not ways of settling the same thing; none holding would say the reading named
     * something no row reaches, which is the shape every misreading of a group ends in.
     */
    private static Map<String, Boolean> takenBy(Interaction group, Observation seen) {
        Map<String, Boolean> settled = new java.util.LinkedHashMap<>();
        for (Factor factor : group.factors()) {
            List<Outcome> did = factor.outcomes().stream()
                    .filter(outcome -> satisfied(outcome, seen))
                    .toList();
            assertEquals(1, did.size(), "the run settled this factor one way: " + factor);
            assertEquals(1, did.get(0).holds().size(),
                    "and this factor is one decision: " + did.get(0));
            Condition what = did.get(0).holds().get(0).constrains();
            Condition.Side side = assertInstanceOf(Condition.Side.class, what,
                    "which the model makes by comparing");
            settled.put(side.at().toString(), side.held());
        }
        return settled;
    }

    private static boolean satisfied(Outcome outcome, Observation seen) {
        return outcome.claims().stream().allMatch(claim -> claim.satisfiedBy(seen));
    }

    /** One model, read the way the generator reads it and run the way an example row is. */
    private record Model(List<Interaction> groups, Behavior behavior) {

        static Model of(String source, String name) {
            Compilation compilation = Compilation.ofSource(source, "Main");
            compilation.answerEverything();
            String module = compilation.modules().get(0);
            Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
            assertNotNull(checked, "the model under test compiles");
            Core body = checked.behaviorBodies().get(name);
            assertNotNull(body, "the behavior under test has a body");
            // The emitter's plan, which is the numbering the classes below were lit against. A plan
            // built here again would be the same numbering and would be a second thing to be right.
            CoverageSites.Plan plan = Output.Evaluated.planOf(compilation.db(), module);
            Symbols symbols = Scopes.derived(compilation.db(), module).value();
            InputDomain inputs =
                    compilation.db().ask(new Adequacy.Inputs(module)).value().get(name);
            souther.compiler.generated.EvaluationArtifact artifact = compilation.db()
                    .ask(new Output.Evaluated(module, ArmObservation.RECORD)).value();
            assertNotNull(artifact, "the model under test emits measured classes");
            return new Model(CoverageRead.of(name, body, plan, inputs, symbols).interactions(),
                    new Behavior(artifact.classes(), module, name));
        }

        Observation observing(Object... arguments) {
            return behavior.observing(arguments);
        }
    }

    /** One set of generated classes, loaded and applied. */
    private static final class Behavior {

        private final Object instance;
        private final Method apply;

        Behavior(Map<String, ClassFileImage> classes, String module, String name) {
            assertNotNull(classes, "the model under test compiles");
            ClassLoader loader = new MemoryClassLoader(classes,
                    AClaimIsWhatARunThatSettledItWouldBeSeenToDoTest.class.getClassLoader());
            try {
                Class<?> impl = Emitted.behavior(loader, module, name);
                Constructor<?> ctor = impl.getDeclaredConstructor();
                ctor.setAccessible(true);
                this.instance = ctor.newInstance();
                this.apply = java.util.Arrays.stream(impl.getDeclaredMethods())
                        .filter(each -> each.getName().equals("apply"))
                        .findFirst()
                        .orElseThrow(() -> new AssertionError("the behavior is applied by `apply`"));
                this.apply.setAccessible(true);
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            }
        }

        Observation observing(Object... arguments) {
            Probe.begin();
            try {
                apply.invoke(instance, arguments);
                return Probe.snapshot();
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            } finally {
                Probe.end();
            }
        }
    }
}
