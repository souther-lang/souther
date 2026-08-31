package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.InputDomain;
import souther.compiler.reading.Interaction;
import souther.compiler.reading.CoverageRead;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every assignment a combination is tried at is one a value can be, and not only the first.
 *
 * <p>A combination is searched at more than one assignment because the first is chosen for what it
 * covers rather than for reaching the meeting, and another may build where it did not. Counted off
 * position by position, the second and third reach assignments no value has — a class under one
 * case of a sum beside a class under another — so a behavior whose sum has positions under two of
 * its cases could be searched at exactly one assignment, and a combination whose first candidate was
 * refused had nowhere left to go.
 */
class AnAlternativeAssignmentIsAsCompatibleAsTheFirstTest {

    /**
     * Two decisions meeting at one sum, beside a parameter with positions under both of its cases.
     *
     * <p>The group is over {@code p} and {@code q}; what the sibling cases add is two positions that
     * cannot both be in one row, which is what the assignments beside the group have to respect.
     */
    private static final String MODEL = """
            module g

            data Yes
            data No
            data Flag = Yes | No

            data Left = { a: Flag }
            data Right = { b: Flag }
            data Either = Left | Right

            data Fee = Int

            behavior fee : (e: Either, p: Flag, q: Flag) -> Fee
                constructs Fee

            let one (f: Flag): Int =
                match f with
                    | Yes -> 1
                    | No -> 0

            let fee (e, p, q) = Fee(one(p) + one(q))
            """;

    private record Model(Generator.Subject subject, CoverageRead.Read read) {

        /** The groups of the one reading, for a caller asking about the combinations alone. */
        List<Interaction> groups() {
            return read.interactions();
        }
    }

    private static Model model() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals("fee")).findFirst().orElseThrow();
        Sig sig = sigs.get("fee");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get("fee");
        Core body = checked.behaviorBodies().get("fee");
        assertNotNull(body);
        CoverageSites.Plan plan = CoverageSites.of(checked.behaviorBodies(), checked.decisions(),
                checked.supplied());
        Partitions.Partitioning axes =
                Partitions.of(spec.name(), inputs, symbols, ReadAs.THE_COMPILATION_DOES);
        return new Model(new Generator.Subject(spec.name(),
                new BehaviorInputs(spec.params().stream().map(Hir.Param::name).toList(),
                        sig.inputTypes(), symbols, ReadAs.THE_COMPILATION_DOES),
                inputs.quantities(symbols), axes.axes()),
                CoverageRead.of(spec.name(), body, plan, inputs, symbols));
    }

    /** The positions under two cases are both axes, which is what the assignments have to hold. */
    @Test
    void bothCasesPutAPositionOnTheList() {
        List<String> at = model().subject().axes().stream()
                .map(each -> each.path().toString()).toList();
        assertTrue(at.contains("e@Left.a") && at.contains("e@Right.b"), at.toString());
    }

    /**
     * A combination whose first assignment is refused is searched at a second one that can be.
     *
     * <p>The refusal is of a value at a position the combination says nothing about, so what has to
     * move is one of the positions beside it — and the assignment that moves it has to leave the
     * sibling case's position where the first one left it, at no class at all.
     */
    @Test
    void aCombinationRefusedAtItsFirstAssignmentIsTriedAtAnother() {
        Model model = model();
        Set<Integer> every = Generator.everyArmACombinationMayTake(model.subject(), model.groups(),
                Budgets.generation());
        assertFalse(every.isEmpty(), "the body has arms a combination takes");

        FillResult filled = Generator.fill(model.subject(), List.of(),
                Generator.CandidateCheck.refusing(AnAlternativeAssignmentIsAsCompatibleAsTheFirstTest::notTheFirst),
                model.read(), Generator.Trial.NOTHING_RUNS, List.of(), List.of(), List.copyOf(every),
                Budgets.generation());

        assertEquals(List.of(), filled.unresolved().stream()
                        .filter(each -> each.reason()
                                == Generator.UnresolvedCombination.Reason.ONE_POSITION_CANNOT_BE_BOTH)
                        .toList(),
                "no combination is refused for naming positions it does not name");
        assertFalse(filled.rows().isEmpty(),
                "and a row is composed at the assignment that was left: " + filled.unresolved());
    }

    /** Refuses the value the first assignment puts at {@code e}, and nothing else. */
    private static Optional<String> notTheFirst(int parameter, FixtureTemplate candidate) {
        return parameter == 0 && candidate.text().equals("Left { a = Yes }")
                ? Optional.of("not this one") : Optional.empty();
    }
}
