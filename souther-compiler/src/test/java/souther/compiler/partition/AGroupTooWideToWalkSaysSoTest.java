package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.InputDomain;
import souther.compiler.interaction.Interaction;
import souther.compiler.interaction.Interactions;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A group of decisions too wide to walk is reported, not dropped.
 *
 * <p>The limit itself is not the subject and neither is its number. What is held here is that
 * exhausting it leaves something a reader can act on: an arm claimed only by a group nothing walked
 * used to leave no entry at all, and an arm with no entry is one no combination claims — so the
 * report said the body never reaches it. That is a statement about the model this compiler had no
 * evidence for, and it is the one thing a limit must never produce.
 *
 * <p>Held against a source rather than by handing a fixture to the search. What decides whether a
 * group is offered is the product of its factors' outcomes, which is read off the body; a fixture
 * naming a group as too wide would be the test saying what the reading is supposed to say.
 */
class AGroupTooWideToWalkSaysSoTest {

    /**
     * As many decisions meeting on one value as it takes to go past the walk.
     *
     * <p>Each parameter is matched by its own helper and every result is added into one {@code Fee},
     * so the thirteen meet at one operator and the group's choices are two to the thirteenth. The
     * offer stops at four thousand and ninety-six and stops <em>at</em> it, so twelve decisions are
     * already the limit and eleven is the last width that is offered — which is what {@link #ELEVEN}
     * is.
     */
    private static final String THIRTEEN = model(13);

    /** The widest model still offered, which is eleven. Without it, a group not offered would be as
     *  good an account of a model this cannot read at all. */
    private static final String ELEVEN = model(11);

    private static String model(int decisions) {
        StringBuilder params = new StringBuilder();
        StringBuilder names = new StringBuilder();
        StringBuilder helpers = new StringBuilder();
        StringBuilder sum = new StringBuilder();
        for (int at = 1; at <= decisions; at++) {
            if (at > 1) {
                params.append(", ");
                names.append(", ");
                sum.append(" + ");
            }
            params.append("p").append(at).append(": Flag");
            names.append("p").append(at);
            sum.append("fee").append(at).append("(p").append(at).append(")");
            helpers.append("""
                    let fee%d (f: Flag): Int =
                        match f with
                            | On  -> %d
                            | Off -> 0

                    """.formatted(at, at));
        }
        return """
                module example.wide

                data On
                data Off
                data Flag = On | Off

                data Fee = Int
                    invariant value >= 0

                behavior total : (%s) -> Fee
                    constructs Fee

                %slet total (%s) = Fee(%s)
                """.formatted(params, helpers, names, sum);
    }

    /**
     * Past the limit, the group is named as one nothing was offered for.
     *
     * <p>Two facts and both are needed. That no group is offered is what the limit does; that the
     * one held back is reported is what this change is. Read off the offered list alone, a model
     * whose decisions this could not read at all looks the same.
     */
    @Test
    void aGroupPastTheLimitIsHeldBackAndSaidSo() {
        Model model = Model.of(THIRTEEN);
        InteractionCells.Offered offered =
                InteractionCells.of(model.groups(), model.subject().axes(), Budgets.generation());

        assertEquals(List.of(), offered.groups(),
                "the group is not offered, which is what the limit is for");
        assertEquals(1, offered.notOffered().size(),
                () -> "and it is named rather than dropped: " + offered.notOffered());
        assertFalse(offered.notOffered().get(0).claims().isEmpty(),
                "carrying what a run through it would have been seen to do");
    }

    /** And one decision fewer is offered, so the answer above is the limit's and not the model's. */
    @Test
    void andUnderTheLimitTheGroupIsOffered() {
        Model model = Model.of(ELEVEN);
        InteractionCells.Offered offered =
                InteractionCells.of(model.groups(), model.subject().axes(), Budgets.generation());

        assertEquals(List.of(), offered.notOffered(),
                "nothing is held back");
        assertFalse(offered.groups().isEmpty(),
                "and the group is there to be walked");
    }

    /**
     * The arms behind a held-back group are arms the combinations take.
     *
     * <p>Which is the half that used to go missing. A caller asking what the combinations reach got
     * a smaller answer because this compiler declined to look, and nothing in the answer said so —
     * so the arms simply were not asked for, and the report about them was that nothing claims them.
     */
    @Test
    void theArmsBehindItAreStillArmsTheCombinationsTake() {
        Model wide = Model.of(THIRTEEN);
        Model narrow = Model.of(ELEVEN);

        Set<Integer> fromWide =
                Generator.everyArmTheCombinationsTake(wide.subject(), wide.groups(), Budgets.generation());
        Set<Integer> fromNarrow =
                Generator.everyArmTheCombinationsTake(narrow.subject(), narrow.groups(), Budgets.generation());

        assertFalse(fromWide.isEmpty(),
                "the arms behind the group the limit held back are still named");
        assertTrue(fromWide.size() > fromNarrow.size(),
                () -> "and a wider body claims more of them, not fewer: " + fromWide.size()
                        + " against " + fromNarrow.size());
    }

    /**
     * And the generation says the walk was not made, in words a row budget does not explain.
     *
     * <p>The reason is what a reader acts on. Told the row limit instead, an author raises a number
     * that changes nothing here — the group was never walked, and no quantity of rows reaches it.
     */
    @Test
    void theGenerationSaysTheWalkWasNotMade() {
        Model model = Model.of(THIRTEEN);

        Generator.GenerationResult composed = Generator.fill(model.subject(), List.of(),
                Generator.CandidateCheck.ANY, model.groups(), Generator.Trial.NOTHING_RUNS, Budgets.generation());

        List<GenerationReason.GroupsNotOffered> said = composed.reasons().stream()
                .filter(GenerationReason.GroupsNotOffered.class::isInstance)
                .map(GenerationReason.GroupsNotOffered.class::cast).toList();
        assertEquals(1, said.size(), () -> "the generation says so once: " + composed.reasons());
        assertEquals(1, said.get(0).groups(), "naming how many groups went unwalked");
        // Every arm behind it is unresolved with that reason, rather than absent — an absent arm is
        // one no combination claims, and that is what this must not be mistaken for.
        List<Generator.ArmAttempt.Unresolved> unresolved = composed.arms().stream()
                .filter(Generator.ArmAttempt.Unresolved.class::isInstance)
                .map(Generator.ArmAttempt.Unresolved.class::cast).toList();
        assertFalse(unresolved.isEmpty(), () -> "the arms are named: " + composed.arms());
        assertTrue(unresolved.stream().allMatch(arm -> arm.why().stream()
                        .anyMatch(why -> why.reason() == Generator.UnresolvedCombination.Reason
                                .THE_GROUP_WAS_NOT_OFFERED)),
                () -> "each saying the walk was never made: " + unresolved);
    }

    /** The behavior's inputs, its axes and the groups its body meets at, off one compile. */
    private record Model(Generator.Subject subject, List<Interaction> groups) {

        static Model of(String source) {
            Compilation compilation = Compilation.ofSource(source, "Main");
            compilation.answerEverything();
            String module = compilation.modules().get(0);
            Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
            Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
            Symbols symbols = Scopes.derived(compilation.db(), module).value();
            Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
            assertNotNull(prepared, "the model compiles");
            assertNotNull(sigs);
            assertNotNull(checked);
            Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                    .filter(b -> b.name().equals("total")).findFirst().orElseThrow();
            InputDomain inputs = compilation.db()
                    .ask(new souther.compiler.query.Adequacy.Inputs(module)).value().get("total");
            assertNotNull(inputs, "the behavior's inputs were read");
            Partitions.Partitioning partitioning = Partitions.of(spec.name(), inputs, symbols,
                    souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
            Core body = checked.behaviorBodies().get("total");
            assertNotNull(body, "the behavior under test has a body");
            CoverageSites.Plan plan = CoverageSites.of(checked.behaviorBodies(), checked.decisions(),
                    checked.supplied());
            return new Model(new Generator.Subject(
                    new BehaviorInputs(spec.params().stream().map(Hir.Param::name).toList(),
                            sigs.get("total").inputTypes(), symbols,
                            souther.compiler.query.ReadAs.THE_COMPILATION_DOES),
                    partitioning.axes(), HeldCounts.of(inputs, symbols)),
                    Interactions.of(body, plan, inputs, symbols));
        }
    }
}
