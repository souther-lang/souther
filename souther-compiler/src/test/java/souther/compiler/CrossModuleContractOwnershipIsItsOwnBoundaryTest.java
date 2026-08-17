package souther.compiler;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassFile;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
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

    private static int invocationsOf(byte[] classBytes, String method, String name) {
        List<String> found = new ArrayList<>();
        ClassFile.of().parse(classBytes).methods().stream()
                .filter(m -> m.methodName().stringValue().equals(method))
                .forEach(m -> m.code().ifPresent(code -> code.forEach(e -> {
                    if (e instanceof InvokeInstruction inv
                            && inv.name().stringValue().equals(name)) {
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

    /**
     * And the module calling it emits no crossing check for it.
     *
     * <p>This is the boundary, stated as what it is. A compilation is the checker of the behaviors it
     * declares; `down` declares none, so `down` enforces none — not because the lookup is missing,
     * but because whether `down` may rely on `up`'s published clause, and under what boundary
     * revision, is not something this stage decides.
     */
    @Test
    void aCallingModuleIsNotTheCheckerOfAnotherModulesContract() {
        Map<String, byte[]> classes = Compiler.compileModules(List.of(DECLARING, CALLING));

        assertEquals(0, invocationsOf(classes.get("down.Use$Impl"), "apply", "check"),
                "`down` is not the checker of `up.fetch`");
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

        assertEquals(1, invocationsOf(classes.get("up.Use$Impl"), "apply", "check"),
                "one module, one checker, one crossing");
    }
}
