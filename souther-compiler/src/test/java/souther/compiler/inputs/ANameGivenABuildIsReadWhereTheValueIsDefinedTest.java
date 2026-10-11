package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A name given a build of a value stands for what the value is defined as, read where a definition
 * is read — in the tree that runs as in the tree an analysis reads, and however the name was given
 * the build.
 *
 * <p>In the tree that runs a value is a call of its method, and what it is defined as is held in the
 * other tree, in the representation that one reads. So a reading of this tree that follows the name
 * is in the definition from there on, read with nothing of this body in force; read here, it would
 * be read under this body's names and in a representation that is not its own.
 */
class ANameGivenABuildIsReadWhereTheValueIsDefinedTest {

    private static final String MODEL = """
            module probe.built

            data Suspect = Alice | Bob | Carol
            let a = Alice
            let b = a

            behavior f : (s: Suspect) -> Bool
            let f (s) = s == b
            """;

    /** The tree that runs, what the analysis reads, and the reading of the input against both. */
    private record Read(Core emitted, AnalysisBody analysis, InputDomain inputs,
                        RuleReadingSource rules, Bodies.Elaborated checked) {

        InputReads reads(ValueDefinitions values) {
            return InputReads.ofParameters(inputs.parameterReads(), inputs.declared(rules),
                    checked.elementBindings().get("f"), values, inputs.dependencies());
        }

        ValueDefinitions values() {
            return ValueDefinitions.of(analysis, rules.newtypes());
        }
    }

    private static Read read() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        Bodies.Elaborated checked =
                compilation.db().ask(new Bodies.Checked("probe.built")).value();
        RuleReadingSource rules = RuleReadings.of(compilation, "probe.built");
        InputDomain inputs =
                compilation.db().ask(new Adequacy.Inputs("probe.built")).value().get("f");
        return new Read(checked.behaviorBodies().get("f"), checked.analysisBodies().get("f"),
                inputs, rules, checked);
    }

    /** Every binding the tree that runs makes of a call of a value's method. */
    private static List<Core.LetIn> buildsIn(Core e) {
        List<Core.LetIn> out = new ArrayList<>();
        collect(e, out);
        return out;
    }

    private static void collect(Core e, List<Core.LetIn> out) {
        if (e instanceof Core.LetIn li && Core.withoutStanding(li.value()) instanceof Core.Call call
                && call.fn() instanceof Core.Reached.OfValue) {
            out.add(li);
        }
        Core.forEachChild(e, child -> collect(child, out));
    }

    private static Core.Read readOf(Core.LetIn li) {
        return new Core.Read(li.binder().name(), li.binder().binding(), li.value().type(),
                li.pos());
    }

    @Test
    void aNameBoundToACallOfAValuesMethodStandsForTheDefinition() {
        Read read = read();
        List<Core.LetIn> builds = buildsIn(read.emitted());
        assertEquals(2, builds.size(), () -> "the tree that runs builds `a` and `b`: " + builds);
        InputReads reads = read.reads(read.values());
        for (Core.LetIn build : builds) {
            InputReads inside = reads.and(build.binder(), build.value());
            Denotation stands = assertInstanceOf(ReadMeaning.Through.class,
                    inside.meaningOf(readOf(build), read.rules().symbols(),
                            read.rules().newtypes())).denotes();
            // What it is defined as is the template the analysis holds, the same tree for every
            // build of it — and read where a definition is, not under this body's names.
            assertSame(read.values().definitionOf(build.value()), stands.value());
            assertEquals(read.values().reading(), stands.at());
            assertNotEquals(inside, stands.at());
        }
    }

    @Test
    void aValueNamedThroughAnotherComesToTheCaseItWasWrittenAs() {
        Read read = read();
        InputReads reads = read.reads(read.values());
        for (Core.LetIn build : buildsIn(read.emitted())) {
            InputReads inside = reads.and(build.binder(), build.value());
            assertInstanceOf(Core.UnitValue.class, Core.withoutStanding(
                    inside.standing(readOf(build), read.rules().symbols(),
                            read.rules().newtypes()).value()),
                    () -> build.binder().name() + " is Alice wherever it is followed to");
        }
    }

    /**
     * Handed to a name rather than bound to it, a build is read the same way. A call handing
     * nothing is held as the value it is; one handing the values it names is held with the reading
     * it was handed in — two ways a name is given a value, and one answer.
     */
    @Test
    void aBuildHandedToANameIsReadAsWhenItIsBound() {
        Read read = read();
        InputReads reads = read.reads(read.values());
        List<Core.LetIn> builds = buildsIn(read.emitted());
        assertEquals(List.of(true, false), builds.stream()
                        .map(each -> ((Core.Call) Core.withoutStanding(each.value())).args()
                                .isEmpty())
                        .sorted(Comparator.reverseOrder()).toList(),
                "one call hands its method nothing and the other hands it a value");
        for (Core.LetIn build : builds) {
            InputReads handed = reads.handing(build.binder().binding(),
                    new Denotation(build.value(), reads), read.rules().newtypes());
            Denotation stands = assertInstanceOf(ReadMeaning.Through.class,
                    handed.meaningOf(readOf(build), read.rules().symbols(),
                            read.rules().newtypes())).denotes();
            assertSame(read.values().definitionOf(build.value()), stands.value(),
                    () -> build.binder().name());
            assertEquals(read.values().reading(), stands.at());
        }
    }

    @Test
    void aBuildNoNameIsGivenIsReadAsWhenOneIs() {
        Read read = read();
        InputReads reads = read.reads(read.values());
        for (Core.LetIn build : buildsIn(read.emitted())) {
            assertInstanceOf(Core.UnitValue.class, Core.withoutStanding(
                    reads.standingValue(build.value(), read.rules().symbols(),
                            read.rules().newtypes()).value()));
        }
    }

    /** The control: told no definitions, the call is a call, which is what says the answers above
     *  are the definitions' and not the tree's. */
    @Test
    void withNoDefinitionsTheCallIsACall() {
        Read read = read();
        InputReads reads = read.reads(ValueDefinitions.NONE);
        Core.LetIn build = buildsIn(read.emitted()).getFirst();
        InputReads inside = reads.and(build.binder(), build.value());
        Denotation stands = assertInstanceOf(ReadMeaning.Through.class,
                inside.meaningOf(readOf(build), read.rules().symbols(),
                        read.rules().newtypes())).denotes();
        assertInstanceOf(Core.Call.class, Core.withoutStanding(stands.value()));
        assertNotNull(stands.at());
    }
}
