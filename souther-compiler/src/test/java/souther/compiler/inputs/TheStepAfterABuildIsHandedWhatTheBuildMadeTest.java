package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A step applied over a list another walk built is handed, on each of its applications, the element
 * that walk made — read in the tree that runs, where the operation that made the list is gone and
 * the walk is what its expansion left.
 *
 * <p>Asked of the reading of an input ({@link InputReads#applicationsOf}) over the step of the last
 * walk, beside the same step over a list written down, which is what the walk's list is to be read
 * as.
 */
class TheStepAfterABuildIsHandedWhatTheBuildMadeTest {

    private static final String MODEL = """
            module w1
            behavior f : (n: Int) -> Ok | No
            let f (n) = {
                let xs = %s
                let ys = List.map(k -> k * n, xs)
                guard List.sum(ys) > 3 else No
                Ok
            }
            """;

    @Test
    void eachApplicationIsHandedWhatTheWalkBeforeItMade() {
        assertEquals(List.of(Optional.of(0L), Optional.of(2L), Optional.of(4L)),
                handedToTheLastStep("List.map(x -> x * 2, [0, 1, 2])"));
        assertEquals(List.of(Optional.of(0L), Optional.of(2L), Optional.of(4L)),
                handedToTheLastStep("[0, 2, 4]"), "the same as the list written down");
    }

    /** What a named closure reads beside its element is read where the closure was written. */
    @Test
    void whatANamedClosureReadsBesideItsElementIsReadWhereItWasWritten() {
        assertEquals(List.of(Optional.of(1L), Optional.of(2L)),
                handedToTheLastStep("{ let offset = 1\n let shift = (x) -> x + offset\n"
                        + " List.map(shift, [0, 1]) }"));
        assertEquals(List.of(Optional.of(0L), Optional.of(1L)),
                handedToTheLastStep("{ let offset = 0\n let shift = (x) -> x + offset\n"
                        + " List.map(shift, [0, 1]) }"));
    }

    /**
     * An element of a filter's list is handed where the filter's step held of it: every element
     * is an application, each kept by that one truth, which a reader decides as it decides any.
     */
    @Test
    void anElementAFilterMadeIsHandedWhereItsStepHeld() {
        String filtered = "List.filter(x -> x > 0, [0, 1, 2])";
        assertEquals(List.of(Optional.of(0L), Optional.of(1L), Optional.of(2L)),
                handedToTheLastStep(filtered));
        InputReads.Applications.Each each = assertInstanceOf(InputReads.Applications.Each.class,
                applicationsOfTheLastStep(filtered));
        assertEquals(List.of(1, 1, 1), each.each().stream()
                .map(made -> made.keptWhere().size()).toList());
        each.each().forEach(made -> assertInstanceOf(ReadMeaning.Occurrence.Kept.ATruth.class,
                made.keptWhere().getFirst()));
    }

    /** A walk an author wrote is one nothing proved what it answers, and the step after it is
     *  handed nothing this reads. */
    @Test
    void aFoldTheAuthorWroteHandsNothingRead() {
        assertInstanceOf(InputReads.Applications.NoneHanded.class,
                applicationsOfTheLastStep("List.fold((acc, x) -> acc ++ [x], [], [0, 1, 2])"));
    }

    /** What each application of the last walk's step hands its element, folded. */
    private static List<Optional<Object>> handedToTheLastStep(String first) {
        Reading read = read(first);
        InputReads.Applications.Each each = assertInstanceOf(InputReads.Applications.Each.class,
                read.applications());
        BindingId element = read.step().params().get(1).binding();
        List<Optional<Object>> out = new ArrayList<>();
        for (InputReads.Applications.Made made : each.each()) {
            out.add(made.reads().folded(new Core.Read("x", element, Type.INT, read.step().pos()),
                    read.rules().symbols(), read.rules().newtypes()));
        }
        return out;
    }

    private static InputReads.Applications applicationsOfTheLastStep(String first) {
        return read(first).applications();
    }

    private record Reading(Core.Block step, InputReads.Applications applications,
                           RuleReadingSource rules) {}

    private static Reading read(String first) {
        Compilation compilation = Compilation.ofSource(MODEL.formatted(first), "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("w1")).value();
        RuleReadingSource rules = RuleReadings.of(compilation, "w1");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("w1")).value().get("f");
        InputReads reads = InputReads.ofParameters(inputs.parameterReads(),
                inputs.declared(rules), checked.elementBindings().get("f"),
                ValueDefinitions.of(checked.analysisBodies().get("f"), rules.newtypes()),
                inputs.dependencies());
        Core body = checked.behaviorBodies().get("f");
        List<Core.Block> steps = new ArrayList<>();
        stepsOfTheWalks(body, steps);
        Core.Block last = steps.getLast();
        InputReads there = readsAt(body, reads, last);
        return new Reading(last, there.applicationsOf(last, rules.symbols(), rules.newtypes(),
                64, ReadMeaning.WhereKept.NOTHING_DECIDED), rules);
    }

    /** {@code reads} with every binding on the way from {@code e} to {@code step} entered, or
     *  null where {@code step} is not in {@code e}. */
    private static InputReads readsAt(Core e, InputReads reads, Core.Block step) {
        if (e == step) {
            return reads;
        }
        if (e instanceof Core.LetIn let) {
            InputReads inValue = readsAt(let.value(), reads, step);
            return inValue != null ? inValue
                    : readsAt(let.body(), reads.and(let.binder(), let.value()), step);
        }
        InputReads[] found = {null};
        Core.forEachChild(e, child -> {
            if (found[0] == null) {
                found[0] = readsAt(child, reads, step);
            }
        });
        return found[0];
    }

    /** The step of every walk the tree that runs holds, in the order the body holds them. */
    private static void stepsOfTheWalks(Core e, List<Core.Block> out) {
        if (e instanceof Core.Call call && call.fn() == Core.Emitted.BUILD_LIST
                && Core.withoutStanding(call.args().getFirst()) instanceof Core.Block step) {
            out.add(step);
        }
        Core.forEachChild(e, child -> stepsOfTheWalks(child, out));
    }
}
