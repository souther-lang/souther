package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.ComparisonOutcome;
import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.ControlPointId;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.Observation;
import souther.compiler.inputs.InputDomain;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;
import souther.compiler.reading.CoverageRead;
import souther.compiler.reading.PathAccess;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a row through an arm comes from, and what one row answers.
 *
 * <p>The way into an arm is the decisions that hold on the way there, and a row steered by them
 * arrives. What that leaves to settle is the rest: which of two places the search looks in first,
 * how one set of values is written down when two arms both came to it, and what says a row goes
 * through an arm it was not composed for.
 */
class ARowThroughAnArmIsComposedFromTheWayIntoItTest {

    /** Two matches, one per input, one nested in the other. Nothing consumes two decided values
     *  into one, so there is no combination to look in and the ways in are all there is. */
    private static final String NESTED = """
            module example.min

            data State = Ready | Running | Paused
            data Button = Start | Reset

            behavior press : (state: State, button: Button) -> State

            let press (state, button) =
                match button with
                    | Start ->
                        match state with
                            | Ready -> Running
                            | Running -> Paused
                            | Paused -> Running
                    | Reset ->
                        match state with
                            | Ready -> Ready
                            | Running -> Running
                            | Paused -> Ready
            """;

    /** Two decisions consumed into one value, so both places to look are there. */
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
     * A body whose decisions meet nowhere still offers a row through every arm.
     *
     * <p>Which is the whole of issue #1009 at the search. Every arm here is one pair of classes
     * away, and both positions divide into the classes that name it — so what was missing was
     * somewhere to look, not something to compose.
     */
    @Test
    void anArmNoCombinationIsOverIsComposedForFromItsWayIn() {
        Model model = Model.of(NESTED, "press");

        FillResult filled = Generator.fill(model.subject(), List.of(),
                Generator.CandidateCheck.ANY, model.read(), Generator.Trial.NOTHING_RUNS,
                List.of(), List.of(), List.copyOf(model.read().arms().keySet()),
                Budgets.generation());

        assertEquals(List.of(), model.read().interactions(),
                "nothing in this body consumes two decided values into one");
        assertFalse(filled.discharge().arms().values().isEmpty(), "and every arm is answered");
        assertTrue(filled.discharge().arms().values().stream().allMatch(ArmDisposition.Built.class::isInstance),
                () -> "with a row through it: " + filled.discharge().arms().values());
        assertTrue(inputsOf(filled).contains(List.of("Ready", "Reset")),
                () -> "including the pair the tutorial's model is short of: " + inputsOf(filled));
        assertTrue(inputsOf(filled).contains(List.of("Running", "Reset")),
                () -> "and the one beside it: " + inputsOf(filled));
    }

    /**
     * Two arms whose searches came to one set of values are one row, offered for both.
     *
     * <p>A row is one line in the file. The searches are the arms' own and neither knows what the
     * other came to, so the same values arriving twice is ordinary — and written down twice, an
     * author is handed the same line under two names and told it answers two different things.
     */
    @Test
    void twoArmsThatCameToOneSetOfValuesAreOneRow() {
        Model model = Model.of(SHIPPING, "shippingFee");

        FillResult filled = Generator.fill(model.subject(), List.of(),
                Generator.CandidateCheck.ANY, model.read(), Generator.Trial.NOTHING_RUNS,
                List.of(), List.of(), List.copyOf(model.read().arms().keySet()),
                Budgets.generation());

        assertEquals(4, model.read().arms().size(), "two arms in each of the two helpers");
        assertTrue(filled.discharge().arms().values().stream().allMatch(ArmDisposition.Built.class::isInstance),
                () -> "each answered: " + filled.discharge().arms().values());
        assertTrue(filled.rows().size() < filled.discharge().arms().values().size(),
                () -> "in fewer rows than there are arms: " + inputsOf(filled));
        assertEquals(filled.rows().size(), new LinkedHashSet<>(inputsOf(filled)).size(),
                () -> "and no two of them are the same line twice: " + inputsOf(filled));
        assertTrue(filled.rows().stream().anyMatch(row -> row.purposes().size() > 1),
                () -> "one row answering two arms says so: " + filled.rows());
    }

    /**
     * What else a row goes through is what watching it says.
     *
     * <p>A row composed for one arm takes every arm on the way to it, and a run that was watched is
     * what shows which. Read off the cell the search happened to look in instead, the reading that
     * composed the row would be certifying itself — and an arm taken off the list that way is one
     * nothing ever went through.
     */
    @Test
    void anotherArmIsTakenOffTheListByWhatTheRunWasSeenDoing() {
        Model model = Model.of(NESTED, "press");
        Set<Integer> everyArm = model.read().arms().keySet();
        Observation everywhere = doing(model.read());

        FillResult watched = Generator.fill(model.subject(), List.of(),
                Generator.CandidateCheck.ANY, model.read(),
                _ -> new Generator.Watched.Ran(everywhere),
                List.of(), List.of(), List.copyOf(everyArm), Budgets.generation());

        assertEquals(1, watched.rows().size(),
                () -> "one row was seen going through every arm, so one row is offered: "
                        + inputsOf(watched));
        assertEquals(everyArm, watched.rows().get(0).purposes().stream()
                        .map(Generator.Purpose.ForAnArm.class::cast)
                        .map(Generator.Purpose.ForAnArm::probe)
                        .collect(Collectors.toCollection(LinkedHashSet::new)),
                "and it is offered for each of them");

        // The same search where nothing watched anything: one row per arm's own way in, and no arm
        // is taken off the list by a reading of where a row would go.
        FillResult unwatched = Generator.fill(model.subject(), List.of(),
                Generator.CandidateCheck.ANY, model.read(), Generator.Trial.NOTHING_RUNS,
                List.of(), List.of(), List.copyOf(everyArm), Budgets.generation());
        assertTrue(unwatched.rows().size() > 1,
                () -> "which nothing here does on the strength of the reading: "
                        + inputsOf(unwatched));
    }

    /**
     * An arm with no way into it is not a search that failed.
     *
     * <p>Two things a reader does different work about. Nothing was composed either way, and what
     * the entry carries is which of them it was: a place no run reaches, or a way in this compiler
     * cannot state. An entry that only said "nothing" left that to whoever read it.
     */
    @Test
    void anArmWithNoWayIntoItSaysWhichKindOfSilenceItIs() {
        Model model = Model.of(NESTED, "press");
        Set<Integer> everyArm = model.read().arms().keySet();

        FillResult filled = Generator.fill(model.subject(), List.of(),
                // Refuses every value, so every way in is a search that ran and composed nothing.
                Generator.CandidateCheck.refusing((_, _) -> java.util.Optional.of("no")),
                model.read(), Generator.Trial.NOTHING_RUNS, List.of(), List.of(), List.copyOf(everyArm),
                Budgets.generation());

        for (int probe : everyArm) {
            assertInstanceOf(ArmDisposition.Unresolved.class, filled.discharge().at(new Generator.ArmOwed(probe)),
                    "a way in this tried and composed nothing at is not one it never had: " + probe);
        }
        assertTrue(model.read().arms().values().stream()
                        .allMatch(PathAccess.Ways.class::isInstance),
                () -> "every arm of this body has a way in: " + model.read().arms());
    }

    /** The values of each row, in the order the row writes them. */
    private static List<List<String>> inputsOf(FillResult filled) {
        return filled.rows().stream()
                .map(row -> row.inputs().stream().map(FixtureTemplate::text).toList())
                .toList();
    }

    /** A run that was seen taking every arm the reading names, which is what a row through the
     *  outer arm and one of the inner ones is seen doing. */
    private static Observation doing(CoverageRead.Read read) {
        Set<Integer> taken = new LinkedHashSet<>();
        Set<ComparisonOutcome> ways = new LinkedHashSet<>();
        for (PathAccess each : read.arms().values()) {
            if (each instanceof PathAccess.Ways ways0) {
                for (souther.compiler.reading.WayIn way : ways0.ways()) {
                    for (ControlClaim claim : way.claims()) {
                        switch (claim.at()) {
                            case ControlPointId.ArmOccurrence arm -> taken.add(arm.probe().getAsInt());
                            case ControlPointId.ComparisonPoint point -> {
                                taken.add(point.at().emissionSite());
                                ways.add(point.way());
                            }
                        }
                    }
                }
            }
        }
        return new Observation(taken, ways);
    }

    private record Model(MeasuredInput subject, CoverageRead.Read read) {

        static Model of(String source, String behavior) {
            Compilation compilation = Compilation.ofSource(source, "Main");
            compilation.answerEverything();
            String module = compilation.modules().get(0);
            Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
            Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
            Symbols symbols = Scopes.derived(compilation.db(), module).value();
            Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
            assertNotNull(checked, "the model under test compiles");
            Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                    .filter(b -> b.name().equals(behavior)).findFirst().orElseThrow();
            InputDomain inputs = compilation.db()
                    .ask(new Adequacy.Inputs(module)).value().get(behavior);
            assertNotNull(inputs, "the behavior's inputs were read");
            Core body = checked.behaviorBodies().get(behavior);
            assertNotNull(body, "the behavior under test has a body");
            CoverageSites.Plan plan = CoverageSites.of(checked.behaviorBodies(), checked.decisions(),
                    checked.supplied());
            Partitions.Partitioning partitioning =
                    Partitions.of(spec.name(), inputs, symbols, ReadAs.THE_COMPILATION_DOES);
            return new Model(MeasuredInput.of(spec.name(), inputs.reading(symbols),
                    partitioning),
                    CoverageRead.of(spec.name(), body, plan, inputs, symbols));
        }
    }
}
