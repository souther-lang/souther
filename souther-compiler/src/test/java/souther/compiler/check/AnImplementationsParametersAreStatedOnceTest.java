package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What a behavior's implementation is required to take, said as a list.
 *
 * <p>The rule is the language's: the {@code let} that implements a behavior takes the behavior's
 * inputs and then the behaviors it depends on, in the order they were declared, and the trailing
 * ones are named by what they inject rather than by whatever the author felt like. That is what
 * E1615 is about, and until now it lived only inside the check that reports it — as two counts added
 * together and an index walked twice — so anything else wanting to know the shape had to work it out
 * again from the signature.
 *
 * <p>The three arms are told apart because a reader has to do something different with each. An
 * input is a position whose name is the author's, so it is a suggestion; an injected one is a
 * position whose name is settled, so it is a name; and a {@code depends on} entry that reaches
 * nothing settles neither, which is reported where it is written and is not a shape anything can be
 * held to.
 */
class AnImplementationsParametersAreStatedOnceTest {

    private static final String TWO_OF_EACH = """
            module example.shape

            data MemberId = String
            data Found = { id: MemberId }
            data Missing = { why: String }

            behavior findMember : (id: MemberId) -> Found | Missing

            behavior logLookup : (id: MemberId) -> Found | Missing

            behavior place : (id: MemberId, other: MemberId) -> Found | Missing
                depends on findMember, logLookup

            let place (id, other, findMember, logLookup) = match findMember(id) with
                | Found   -> logLookup(other)
                | Missing -> findMember(other)
            """;

    private static final String NO_DEPENDENCIES = """
            module example.plain

            data MemberId = String
            data Found = { id: MemberId }

            behavior name : (id: MemberId, fallback: MemberId) -> Found
                constructs Found

            let name (id, fallback) = Found { id = id }
            """;

    /** The inputs first, in declared order, then what is injected, in declared order. */
    @Test
    void theInputsComeFirstAndTheInjectedOnesFollowInDeclaredOrder() {
        assertEquals(List.of(
                        new SpecImplementation.Parameter.Input("id"),
                        new SpecImplementation.Parameter.Input("other"),
                        new SpecImplementation.Parameter.Injected("findMember"),
                        new SpecImplementation.Parameter.Injected("logLookup")),
                SpecImplementation.parameters(behaviorOf(TWO_OF_EACH, "place")));
    }

    /** A behavior that depends on nothing is its inputs and nothing else. */
    @Test
    void aBehaviorThatDependsOnNothingIsItsInputs() {
        assertEquals(List.of(
                        new SpecImplementation.Parameter.Input("id"),
                        new SpecImplementation.Parameter.Input("fallback")),
                SpecImplementation.parameters(behaviorOf(NO_DEPENDENCIES, "name")));
    }

    /**
     * And it is the same list the implementation was accepted against.
     *
     * <p>Both of these models compile, so their {@code let}s satisfied E1615. Holding the list to
     * what those {@code let}s were written with is what says this states the rule the checker
     * applies rather than a second reading of the signature that happens to agree today.
     */
    @Test
    void theListIsWhatAnAcceptedImplementationWasWrittenWith() {
        assertEquals(List.of("id", "other", "findMember", "logLookup"),
                writtenParametersOf(TWO_OF_EACH, "place"));
        assertEquals(List.of("id", "fallback"), writtenParametersOf(NO_DEPENDENCIES, "name"));
    }

    /**
     * An implementation that does not take the list is refused, and refused for taking the wrong
     * number of parameters.
     *
     * <p>Here because nothing else asserted it. The rule the list states is the rule E1615 enforces,
     * and a list that stopped counting the injected positions would leave every implementation
     * accepted with too few parameters — which the models above, all of which compile, cannot show.
     */
    @Test
    void anImplementationThatDoesNotTakeTheListIsRefused() {
        CompileException tooFew = assertThrows(CompileException.class,
                () -> Compiler.compile(TWO_OF_EACH.replace(
                        "let place (id, other, findMember, logLookup)", "let place (id, other)")));
        assertEquals("E1615", tooFew.code(), "an implementation short of its injected parameters");
    }

    /** And one that takes them in another order is refused for that. */
    @Test
    void anInjectedParameterOutOfOrderIsRefused() {
        CompileException swapped = assertThrows(CompileException.class,
                () -> Compiler.compile(TWO_OF_EACH.replace(
                        "let place (id, other, findMember, logLookup)",
                        "let place (id, other, logLookup, findMember)")));
        assertEquals("E1615", swapped.code(), "the injected parameters are named in declared order");
    }

    private static Hir.SpecBehavior behaviorOf(String source, String name) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        assertNotNull(prepared, "the model under test compiles");
        return (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(behavior -> behavior.name().equals(name))
                .findFirst().orElseThrow();
    }

    /** What the accepted implementation of {@code name} was actually written with. */
    private static List<String> writtenParametersOf(String source, String name) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        assertNotNull(prepared, "the model under test compiles");
        return prepared.fns().stream()
                .filter(fn -> fn.read().name().equals(name))
                .findFirst().orElseThrow()
                .read().params().stream().map(Hir.FnParam::name).toList();
    }
}
