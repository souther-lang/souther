package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.ComparisonOutcome;
import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.Observation;
import souther.compiler.coverage.ControlPointId;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.InputDomain;
import souther.compiler.interaction.Interaction;
import souther.compiler.interaction.Interactions;
import souther.compiler.observe.Classification;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What fills a combination of a body's decisions, and what only looks like it.
 *
 * <p>A combination is a path through the body and an outcome at each decision that meets on it. What
 * fills one is a run that took that path and settled them those ways. Sitting in the classes the
 * combination leaves open is what the reading expected of such a run — and the step from the
 * decisions to the classes is a reading, which can be wrong while looking right.
 *
 * <p>So this puts the same row in twice, once with a run behind it and once with nothing, and asks
 * what is still owed. The row's values are the same both times; only whether anything watched it
 * differs.
 */
class ARowNothingRanFillsNoCombinationTest {

    /** Two decisions, one per input, consumed into one value. Both are matched on, so the classes a
     * row sits in are the declared cases and no threshold is needed to divide anything. */
    private static final String SHIPPING = """
            module example.shipping

            data Membership = Premium | Standard

            data Delivery = Express | Regular

            data Fee = Int
                invariant value >= 0

            behavior shippingFee : (member: Membership, delivery: Delivery) -> Fee
                constructs Fee

            let baseFee (tier: Membership): Int =
                match tier with
                    | Premium -> 0
                    | Standard -> 500

            let expressFee (speed: Delivery): Int =
                match speed with
                    | Express -> 500
                    | Regular -> 0

            let shippingFee (member, delivery) =
                Fee(baseFee(member) + expressFee(delivery))
            """;

    /**
     * A combination is where an arm's row is looked for, and is not itself owed one.
     *
     * <p>This used to be about which rows filled a combination: seen doing what it names it filled
     * one, seen doing something else it did not, and where nothing could watch it an author's row
     * was given the benefit. All three were the generator counting rows against a space nothing
     * reports — and it counted them from a reading of the body, which is what could be wrong.
     *
     * <p>The three answers are still there and they are one measure's: whether an arm was reached
     * is what {@code BranchEvidence} establishes, and an arm nothing read the rows for is not
     * established as unreached at all. What is left here is that the search looks where it is told
     * to and composes for nothing of its own.
     */
    @Test
    void aCombinationIsSearchedForAnArmOnTheListAndForNothingElse() {
        Model model = Model.of(SHIPPING, "shippingFee");
        List<InteractionCells.Group> groups =
                InteractionCells.of(model.groups(), model.subject().axes());
        assertEquals(1, groups.size(), "the two decisions meet once");
        CellSelection first = groups.get(0).at(0);
        assertNotNull(first, "and its first choice is a combination");
        assertFalse(first.claims().isEmpty(), "which a run can be held to");

        Map<AxisId, Classification> sitting = at(model.subject().axes(), first);
        String combination = labelOf(model.subject().axes(), sitting);

        assertTrue(offeredFor(model, Generator.everyArmTheCombinationsTake(
                        model.subject(), model.groups())).contains(combination),
                "asked about the arms this combination takes, a row is composed for it");
        assertFalse(offeredFor(model, java.util.Set.of()).contains(combination),
                "and asked about none of them, nothing here composes for the combination itself");
    }

    /**
     * A class is composed for when it is on the list, and no class is on it by the search's doing.
     *
     * <p>The same question the arms are asked, at the other measure. Which classes are owed a row is
     * what the partition measure reads off the rows, and a search working it out again for itself
     * is a second reading of one fact — free to offer an author a row at a class the report calls
     * reached, or to say nothing at one it calls unreached.
     */
    @Test
    void aClassIsComposedForWhenItIsOnTheListAndNotOtherwise() {
        Model model = Model.of(SHIPPING, "shippingFee");
        Set<Generator.ClassOwed> every =
                Generator.everyClassNoRowSitsIn(model.subject(), List.of());
        assertFalse(every.isEmpty(), "the model divides its positions");
        Generator.ClassOwed one = every.iterator().next();

        assertEquals(List.of(), composedFor(model, Set.of()),
                "asked for no class, nothing is composed");
        assertEquals(List.of(one), composedFor(model, Set.of(one)),
                "and asked for one, that one and nothing beside it");
    }

    /** Which classes the generator composes a row for when it is asked about {@code classes}. */
    private static List<Generator.ClassOwed> composedFor(Model model,
                                                         Set<Generator.ClassOwed> classes) {
        return Generator.fill(model.subject(), List.of(), Generator.CandidateCheck.ANY,
                        model.groups(), Generator.Trial.NOTHING_RUNS, List.of(), classes,
                        java.util.Set.of())
                .rows().stream().map(Generator.GeneratedRow::purpose)
                .map(Generator.Purpose.ForAClass.class::cast)
                .map(at -> new Generator.ClassOwed(at.at(), at.classId())).toList();
    }

    /** What the generator offers when it is asked about {@code arms}, as the classes of each. */
    private static List<String> offeredFor(Model model, java.util.Set<Integer> arms) {
        return Generator.fill(model.subject(), List.of(), Generator.CandidateCheck.ANY,
                        model.groups(), Generator.Trial.NOTHING_RUNS, List.of(),
                        Generator.everyClassNoRowSitsIn(model.subject(), List.of()), arms)
                .rows().stream().map(Generator.GeneratedRow::description).toList();
    }

    /** One class per divided position, taken from the one class the combination leaves there. */
    private static Map<AxisId, Classification> at(List<Axis> axes, CellSelection selection) {
        Map<AxisId, Classification> out = new java.util.LinkedHashMap<>();
        for (int i = 0; i < axes.size(); i++) {
            out.put(axes.get(i).id(), Classification.in(axes.get(i).classes().get(only(selection, i))
                    .id()));
        }
        return out;
    }

    /** Which single class the combination leaves the position, the model having one per outcome. */
    private static int only(CellSelection selection, int axis) {
        for (int c = 0; c < selection.cell().allowed()[axis].length; c++) {
            if (selection.cell().admits(axis, c)) {
                return c;
            }
        }
        throw new AssertionError("a combination leaves every position something");
    }

    /** How the generator names a row sitting at these classes. */
    private static String labelOf(List<Axis> axes, Map<AxisId, Classification> sitting) {
        List<String> parts = axes.stream()
                .map(axis -> axis.term() + "="
                        + String.join("|", ((Classification.Classified) sitting.get(axis.id())).classIds()))
                .toList();
        return String.join(" x ", parts);
    }

    /** A run that did everything {@code claims} names and nothing else. */
    private static Observation doing(List<ControlClaim> claims) {
        Set<Integer> taken = new LinkedHashSet<>();
        Set<ComparisonOutcome> ways = new LinkedHashSet<>();
        for (ControlClaim claim : claims) {
            switch (claim.at()) {
                case ControlPointId.ArmOccurrence arm -> taken.add(arm.probe().getAsInt());
                case ControlPointId.ComparisonPoint point -> {
                    taken.add(point.at().emissionSite());
                    ways.add(point.way());
                }
            }
        }
        return new Observation(taken, ways);
    }

    private record Model(Generator.Subject subject, List<Interaction> groups) {

        static Model of(String source, String behavior) {
            Compilation compilation = Compilation.ofSource(source, "Main");
            compilation.answerEverything();
            String module = compilation.modules().get(0);
            Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
            Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
            Symbols symbols = Scopes.derived(compilation.db(), module).value();
            Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
            assertNotNull(prepared);
            assertNotNull(sigs);
            assertNotNull(checked);
            Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                    .filter(b -> b.name().equals(behavior)).findFirst().orElseThrow();
            Sig sig = sigs.get(behavior);
            InputDomain inputs = compilation.db()
                    .ask(new souther.compiler.query.Adequacy.Inputs(module)).value()
                    .get(behavior);
            assertNotNull(inputs, "the behavior's inputs were read");
            Partitions.Partitioning partitioning = Partitions.of(spec.name(), inputs, symbols,
                    souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
            Core body = checked.behaviorBodies().get(behavior);
            assertNotNull(body, "the behavior under test has a body");
            CoverageSites.Plan plan = CoverageSites.of(checked.behaviorBodies(), checked.decisions(),
                checked.supplied());
            return new Model(new Generator.Subject(
                    new BehaviorInputs(spec.params().stream().map(Hir.Param::name).toList(),
                            sig.inputTypes(), symbols,
                            souther.compiler.query.ReadAs.THE_COMPILATION_DOES),
                    partitioning.axes(), HeldCounts.of(inputs, symbols)),
                    Interactions.of(body, plan, inputs, symbols));
        }
    }
}
