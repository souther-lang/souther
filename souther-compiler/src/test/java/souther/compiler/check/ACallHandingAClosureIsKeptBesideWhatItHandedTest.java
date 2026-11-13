package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.core.Core;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.ACallOfAnOperation;
import souther.compiler.types.BindingId;
import souther.compiler.types.ValueName;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Which call handed a closure what it holds is kept beside what was handed and never in it: one
 * container handed by two calls is one thing held, as it was, and both calls are kept.
 *
 * <p>No source writes one block handed by two calls — a closure is a block where a call writes
 * it — so the body here is a compiled one with the second call handed the first one's block and
 * container, standing where it stands.
 */
class ACallHandingAClosureIsKeptBesideWhatItHandedTest {

    private static final String MODEL = """
            module demo

            behavior f : (b: Bool, xs: List<Int>) -> List<Int>
            let f (b, xs) = if b then List.map(x -> x + 1, xs) else List.map(x -> x + 2, xs)
            """;

    private static Core.PreservedCall aCall(Core e) {
        return assertInstanceOf(Core.PreservedCall.class, Core.withoutStanding(e),
                "an operation of the language kept standing as a call");
    }

    private static BindingId parameterOf(Core.PreservedCall call) {
        for (Core argument : call.args()) {
            if (Core.withoutStanding(argument) instanceof Core.Block block) {
                return block.params().getFirst().binding();
            }
        }
        throw new AssertionError("the call is handed a block: " + call);
    }

    private static ACallOfAnOperation of(Core.PreservedCall call) {
        return new ACallOfAnOperation((ValueName.Stdlib) call.declared().operation(),
                call.occurrence());
    }

    @Test
    void oneContainerHandedByTwoCallsIsOneThingHeldAndTwoCalls() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        ACompiledModel.compiles(compilation);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        assertNotNull(checked, "the model compiles");
        DeclarationNewtypes newtypes = RuleReadings.of(compilation, "demo").newtypes();
        Core.If fork = assertInstanceOf(Core.If.class,
                Core.withoutStanding(checked.analysisBodies().get("f").core()));
        Core.PreservedCall first = aCall(fork.then());
        Core.PreservedCall second = aCall(fork.els());
        assertNotEquals(first.occurrence(), second.occurrence(), "two calls the source wrote");
        BindingId element = parameterOf(first);

        // The second call, standing where it stands, handed what the first is handed.
        Core.PreservedCall handingTheSame = new Core.PreservedCall(second.declared(),
                first.args(), second.place(), second.settled(), second.type(), second.pos());
        Core both = new Core.If(fork.cond(), fork.then(), handingTheSame, fork.place(),
                fork.type(), fork.pos());

        ElementBindings once = ElementBindings.of(fork, ElementProvenance.NONE, newtypes);
        ElementBindings twice = ElementBindings.of(both, ElementProvenance.NONE, newtypes);
        assertEquals(Set.of(of(first)), once.handedBy(element));
        assertEquals(Set.of(of(first), of(handingTheSame)), twice.handedBy(element),
                "both calls, whichever of them what was handed is kept from");
        assertEquals(1, twice.containersOf(element).size(), "one container, one thing held");
        assertEquals(once.containersOf(element), twice.containersOf(element),
                "and held as it is held when one call hands it: no call is part of it");
    }
}
