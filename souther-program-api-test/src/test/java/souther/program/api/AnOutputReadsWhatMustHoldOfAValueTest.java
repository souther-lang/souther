package souther.program.api;

import souther.compiler.core.Contract;
import souther.compiler.core.Core;
import souther.compiler.core.EnsuresEnforcement;
import souther.compiler.core.ValueShape;
import souther.compiler.program.CheckedBehavior;
import souther.compiler.program.CheckedData;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.types.BindingId;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an output that is not this compiler learns about the two conditions the language states.
 *
 * <p>A build that emits a construction without them admits a value the JVM refuses, and one whose
 * behaviors are held to nothing refuses programs the JVM accepts. Neither is a decision an output
 * gets to make, and until #1080 neither could be read from here: both were the syntax tree the
 * checker read, which does not cross this boundary at all.
 *
 * <p>What is held here is that they cross as what runs — the condition the checker elaborated, over
 * bindings the same answer names — so an output emitting from this and the JVM emitting from its
 * own copy of the same answer cannot come to admit different values.
 */
class AnOutputReadsWhatMustHoldOfAValueTest {

    /** A module whose clauses are written where they are checked. */
    private static final String DECLARING = """
            module up exposing ( Common, Amount, halve )

            data Amount = Int
                invariant positive = value > 0

            data Common =
                { id: Int
                , tag: String
                }
                invariant identified = id > 0

            behavior halve : (a: Amount) -> Amount
                ensures smaller = value.value < a.value

            let halve (a) = Amount(a.value / 2)

            behavior name : (a: Amount) -> String

            let name (a) = "amount"
            """;

    /** And a module that takes one of them in, so the clause is checked where a value is built and
     *  not where it was written. */
    private static final String INCLUDING = """
            module down

            import up ( Common )

            data Wide =
                { ...Common
                , extra: Int
                }
                invariant wide = extra > id
            """;

    private static CheckedProgram program() {
        return CheckedProgram.of(List.of(DECLARING, INCLUDING));
    }

    private static CheckedData.Product product(CheckedModule module, String name) {
        for (CheckedData each : module.data()) {
            if (each.name().name().equals(name)) {
                return assertInstanceOf(CheckedData.Product.class, each, name);
            }
        }
        throw new AssertionError(name + " is not among this module's data");
    }

    private static CheckedBehavior behavior(CheckedModule module, String name) {
        for (CheckedBehavior each : module.behaviors()) {
            if (each.name().name().equals(name)) {
                return each;
            }
        }
        throw new AssertionError(name + " is not among this module's behaviors");
    }

    @Test
    void aProductSaysWhatMustHoldOfAValueOfIt() {
        CheckedData.Product amount = product(program().module("up"), "Amount");

        assertEquals(1, amount.invariants().size(), "one clause is declared of it");
        assertEquals("positive", amount.invariants().get(0).name().orElse(null),
                "under the name a failure is reported by");
        assertNotNull(amount.invariants().get(0).condition(),
                "and what has to hold, as the checker elaborated it");
    }

    /** A data nothing is stated of says so by stating nothing, which is not a data with no fields. */
    @Test
    void aProductWithNoClauseStatesNothing() {
        CheckedData.Product common = product(program().module("up"), "Common");

        assertEquals(List.of("identified"),
                common.invariants().stream().map(each -> each.name().orElse("")).toList());
    }

    /**
     * A clause reads its fields through the bindings the same answer names.
     *
     * <p>The half that makes a clause runnable. An output puts each field's value under the binding
     * {@link CheckedData.Product#fields()} gives it and emits the condition; a binding the condition
     * reads and the fields do not name is a value nothing put anywhere, and the check would run over
     * whatever happened to be in that slot.
     */
    @Test
    void everyBindingAClauseReadsIsAFieldOfWhatItIsAbout() {
        for (CheckedModule module : program().modules()) {
            for (CheckedData declared : module.data()) {
                if (!(declared instanceof CheckedData.Product product)) {
                    continue;
                }
                Set<BindingId> bound = new LinkedHashSet<>();
                for (ValueShape.Field field : product.fields()) {
                    bound.add(field.binding());
                }
                for (ValueShape.Invariant clause : product.invariants()) {
                    assertTrue(bound.containsAll(read(clause.condition())),
                            () -> "`" + product.name() + "` states " + clause.name()
                                    + " over " + read(clause.condition())
                                    + ", and holds " + bound);
                }
            }
        }
    }

    /**
     * And that holds of a clause another module wrote.
     *
     * <p>The case the answer is keyed by the data being built rather than by the declaration a
     * clause was written on. {@code Wide} takes {@code Common} in and is held to {@code Common}'s
     * clause where a value of {@code Wide} is built; the binding that clause reads is the one
     * {@code up} gave the field, and it is among {@code Wide}'s fields because a field brought in by
     * an include keeps the binding of the declaration that wrote it.
     */
    @Test
    void aClauseAnIncludeBroughtInIsStatedOfTheDataBeingBuilt() {
        CheckedData.Product wide = product(program().module("down"), "Wide");

        assertEquals(List.of("identified", "wide"),
                wide.invariants().stream().map(each -> each.name().orElse("")).toList(),
                "what it takes in comes first, which is the order a failure is decided in");

        Set<BindingId> bound = new LinkedHashSet<>();
        for (ValueShape.Field field : wide.fields()) {
            bound.add(field.binding());
        }
        Core brought = wide.invariants().get(0).condition();
        assertTrue(bound.containsAll(read(brought)),
                () -> "the clause `up` wrote reads " + read(brought) + " of " + bound);
    }

    @Test
    void aBehaviorSaysWhatItDeclaresOfItsAnswerAndWhereThatIsChecked() {
        CheckedBehavior halve = behavior(program().module("up"), "halve");

        EnsuresEnforcement.AtTheCallee where = assertInstanceOf(
                EnsuresEnforcement.AtTheCallee.class, halve.ensures(),
                "it has a body here, so its own answer is where the check goes");
        Contract states = where.contract();
        assertEquals(1, states.rules().size(), "one rule, specialized once");
        assertEquals("smaller", states.rules().get(0).clause().orElse(null),
                "under the clause a violation is reported by");
        assertNotNull(states.rules().get(0).condition(), "and what has to hold of the answer");
        assertEquals(List.of("a"), states.params().stream().map(Contract.Param::name).toList(),
                "over the parameters the rule names");
    }

    /** A behavior that declares nothing says that, and it is not the answer for a behavior nobody
     *  decided about. */
    @Test
    void aBehaviorThatDeclaresNothingSaysSo() {
        assertInstanceOf(EnsuresEnforcement.NoContract.class,
                behavior(program().module("up"), "name").ensures());
    }

    /** Every binding {@code condition} reads. */
    private static Set<BindingId> read(Core condition) {
        Set<BindingId> found = new LinkedHashSet<>();
        collect(condition, found);
        return found;
    }

    private static void collect(Core node, Set<BindingId> found) {
        if (node instanceof Core.Read read) {
            found.add(read.binding());
        }
        List<Core> children = new ArrayList<>();
        Core.forEachChild(node, children::add);
        for (Core child : children) {
            collect(child, found);
        }
    }
}
