package souther.compiler.query;

import souther.compiler.Compiler;
import souther.compiler.core.EnsuresEnforcement;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassFile;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A contract belongs to the compilation that owns the behavior, and reaching across a module
 * boundary for one is a different question from checking it.
 *
 * <p>What is settled here is which behaviors a compilation is the checker of: the ones it declares.
 * For those, the check is emitted in exactly one place — the behavior's own {@code apply}, or the
 * crossing each caller makes — and that is the whole of what this stage is responsible for.
 *
 * <p>A behavior another module declared is outside that. Its clause is checked where its module says
 * it is, and a caller here reaching for it would need more than the clause: which boundary revision
 * the artifact was published under, whether what it published is an executable guarantee at all, and
 * on what basis this compilation may rely on it. Those are questions about who owns a contract across
 * a boundary, and the answer is a model of that ownership rather than a lookup. Answering it by
 * reading a module name would decide it by a spelling.
 *
 * <p>So this is not a gap left where a check was meant to go. It is the edge of what a compilation
 * claims to enforce, and it is written down so that the day cross-module ownership is designed, what
 * changes is a decision somebody made rather than a behavior somebody discovers.
 */
class CrossModuleContractOwnershipIsItsOwnBoundaryTest {

    private static final String DECLARING = """
            module up exposing ( Amount, fetch )

            data Amount = Int

            behavior fetch : (a: Amount) -> Amount
                ensures doubled = value.value == a.value * 2
            """;

    private static final String CALLING = """
            module down

            import up ( Amount, fetch )

            behavior use : (a: Amount) -> Amount
                depends on fetch
            let use (a, fetch) = fetch(a)
            """;

    /** How many times {@code classBytes} calls {@code owner}'s {@code check}, over every method it
     *  has. The owner is counted, so a call to some other behavior's check is not read as this one. */
    private static int checksOf(byte[] classBytes, String owner) {
        List<String> found = new ArrayList<>();
        ClassFile.of().parse(classBytes).methods()
                .forEach(m -> m.code().ifPresent(code -> code.forEach(e -> {
                    if (e instanceof InvokeInstruction inv
                            && inv.name().stringValue().equals("check")
                            && inv.owner().name().stringValue().equals(owner)) {
                        found.add(inv.owner().name().stringValue());
                    }
                })));
        return found.size();
    }

    /** The module that declares the clause carries it, and carries it whoever ends up calling it. */
    @Test
    void theDeclaringModuleCarriesTheCheck() {
        Map<String, byte[]> classes = Compiler.compileModules(List.of(DECLARING, CALLING));

        assertTrue(classes.containsKey("up.Fetch$Ensures"),
                "the clause is `up`'s, so the class holding it is: " + classes.keySet());
    }

    /** The decisions `down`'s compilation reached, as the emitter was handed them. */
    private static EnsuresEnforcement decidedByDown(ValueName.Behavior about) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("up.sou", DECLARING);
        byId.put("down.sou", CALLING);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        Output.Classes.Inputs in = Output.Classes.inputs(c.db(), "down");
        return EnsuresEnforcement.in(in.checks(), "down", about);
    }

    /**
     * What `down` decided about `up.fetch` is that it did not decide.
     *
     * <p>The subject of this test is the classification and not the count. A count of zero is what
     * the decision comes to today, and on its own it says the same thing a behavior with no clause at
     * all says — so fixing the count would fix an observation while leaving what produced it unsaid,
     * and the reason would be gone the first time somebody read it back.
     *
     * <p>`up.fetch` declares a clause and has no body, so its own module cannot check it where it
     * answers, and `down` is where the crossing is. Whether `down` may run `up`'s published check —
     * under which boundary revision, on what basis that artifact's clause is an executable guarantee
     * at all — is an ownership model this stage has not got. So `down` answers that it has not
     * decided, which is a different answer from there being nothing to check, and the day the model
     * exists this is the answer that changes.
     */
    @Test
    void aCallingModuleHasNotDecidedAboutAnotherModulesContract() {
        assertInstanceOf(EnsuresEnforcement.NotDecidedHere.class,
                decidedByDown(new ValueName.Behavior("up", "fetch")),
                "`down` has not decided about `up.fetch`, rather than decided there is no check");

        Map<String, byte[]> classes = Compiler.compileModules(List.of(DECLARING, CALLING));
        assertEquals(0, checksOf(classes.get("down.Use$Impl"), "up/Fetch$Ensures"),
                "and so emits nothing for it — which follows from the decision above");
    }

    /**
     * A table with nothing under a name of its own is not an answer, and says so.
     *
     * <p>Written here because nothing in the suite reaches it: this compilation decides about every
     * behavior it declares, so the state is one no input produces, and a mechanism whose data never
     * takes that shape is a mechanism nothing has run. What it guards is a table that was not filled
     * — a local behavior with a clause would otherwise take the foreign answer, emit no check, and
     * read as a boundary somebody had reasoned about.
     */
    @Test
    void aNameOfItsOwnWithNoDecisionIsNotAnAnswer() {
        ValueName.Behavior ofItsOwn = new ValueName.Behavior("down", "use");

        IllegalStateException thrown = assertThrows(IllegalStateException.class,
                () -> EnsuresEnforcement.in(Map.of(), "down", ofItsOwn));
        assertTrue(thrown.getMessage().contains("use"), thrown.getMessage());

        assertInstanceOf(EnsuresEnforcement.NotDecidedHere.class,
                EnsuresEnforcement.in(Map.of(), "down", new ValueName.Behavior("up", "fetch")),
                "the same empty table answers for a name from elsewhere, which is the difference");
    }

    /** A behavior of its own that states nothing is the other answer: decided, and there is no
     *  check. The two would be one value if absence stood for both. */
    @Test
    void aBehaviorOfItsOwnThatStatesNothingIsDecided() {
        assertInstanceOf(EnsuresEnforcement.NoContract.class,
                decidedByDown(new ValueName.Behavior("down", "use")),
                "`down` read `use` and found no clause");
    }

    /** The same behavior, declared and called in one module, is checked at the crossing — which is
     *  what says the difference above is the module boundary and not the shape of the call. */
    @Test
    void theSameCallWithinOneModuleIsCheckedAtItsCrossing() {
        Map<String, byte[]> classes = Compiler.compile("""
                module up

                data Amount = Int

                behavior fetch : (a: Amount) -> Amount
                    ensures doubled = value.value == a.value * 2

                behavior use : (a: Amount) -> Amount
                    depends on fetch
                let use (a, fetch) = fetch(a)
                """);

        assertEquals(1, checksOf(classes.get("up.Use$Impl"), "up/Fetch$Ensures"),
                "one module, one checker, one crossing");
    }
}
