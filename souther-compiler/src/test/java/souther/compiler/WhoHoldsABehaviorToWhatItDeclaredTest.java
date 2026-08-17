package souther.compiler;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassFile;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which bytecode carries a behavior's check, and how many times.
 *
 * <p>A clause is checked in exactly one of two places, and which one is decided by whether the
 * behavior's body is this compiler's to emit. A bodied behavior holds itself: its {@code apply} is
 * the one door every application goes through, so no caller emits anything. An injected one has no
 * body here — a Java implementation supplies {@code apply} (ADR-0056) — so what holds it is the
 * crossing, in the caller's own bytecode, on the line the Decoder draws for a value arriving from
 * outside.
 *
 * <p>Counted rather than merely looked for. "Checked somewhere" is satisfied by a clause checked
 * twice, which is silent and costs a run on every call, and by one checked in the wrong place, which
 * is silent until the other door is used.
 */
class WhoHoldsABehaviorToWhatItDeclaredTest {

    /**
     * How many times {@code classBytes} calls {@code owner}'s {@code check}, over every method it
     * has.
     *
     * <p>The owner is what is counted and not merely the name, because a class calling some other
     * behavior's check is not this class holding that one. And every method rather than
     * {@code apply}, because which method the call sits in is what this change moves: a caller that
     * gains a clause of its own has its body moved under {@code apply$body} and takes the crossing
     * with it, so a count over {@code apply} alone would quietly go to zero and read as "nothing is
     * checked here".
     */
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

    /** The same, said of one method — for the two places that are about which method holds it. */
    private static int checksIn(byte[] classBytes, String method, String owner) {
        List<String> found = new ArrayList<>();
        ClassFile.of().parse(classBytes).methods().stream()
                .filter(m -> m.methodName().stringValue().equals(method))
                .forEach(m -> m.code().ifPresent(code -> code.forEach(e -> {
                    if (e instanceof InvokeInstruction inv
                            && inv.name().stringValue().equals("check")
                            && inv.owner().name().stringValue().equals(owner)) {
                        found.add(inv.owner().name().stringValue());
                    }
                })));
        return found.size();
    }

    /** A behavior with a body, and one calling it by name. Both are this module's, so nothing is
     *  injected — a behavior that depends on nothing is reached by name rather than handed over. */
    private static final String BODIED = """
            module demo

            data Amount = Int

            behavior twice : (a: Amount) -> Amount
                constructs Amount
                ensures doubled = value.value == a.value * 2
            let twice (a) = Amount { value = a.value * 2 }

            behavior twiceOver : (a: Amount) -> Amount
            let twiceOver (a) = twice(a)
            """;

    /** `fetch` has no `let`, so a Java implementation supplies it: the answer enters at the call. */
    private static final String INJECTED = """
            module demo

            data Amount = Int

            behavior fetch : (a: Amount) -> Amount
                ensures doubled = value.value == a.value * 2

            behavior use : (a: Amount) -> Amount
                depends on fetch
            let use (a, fetch) = fetch(a)
            """;

    @Test
    void aBodiedBehaviorChecksItselfOnceWhereItAnswers() {
        Map<String, byte[]> classes = Compiler.compile(BODIED);

        assertEquals(1, checksIn(classes.get("demo.Twice$Impl"), "apply", "demo/Twice$Ensures"),
                "its own `apply` is the door every application goes through");
        assertEquals(0, checksIn(classes.get("demo.Twice$Impl"), "apply$body", "demo/Twice$Ensures"),
                "and the body is what is being held, not where the holding is written");
    }

    /** A caller emits nothing: what it calls holds itself, whatever door the caller came in by. */
    @Test
    void acallerOfABodiedBehaviorEmitsNoCheck() {
        Map<String, byte[]> classes = Compiler.compile(BODIED);

        assertEquals(0, checksOf(classes.get("demo.TwiceOver$Impl"), "demo/Twice$Ensures"),
                "`twice` is checked by `twice`, in none of this class's methods");
    }

    @Test
    void anInjectedBehaviorIsCheckedAtTheCrossingByWhoeverCallsIt() {
        Map<String, byte[]> classes = Compiler.compile(INJECTED);

        assertEquals(1, checksOf(classes.get("demo.Use$Impl"), "demo/Fetch$Ensures"),
                "the answer enters the domain here, so this is where it is held");
    }

    /**
     * The class the check lives in is emitted by the module that declares the behavior, whichever of
     * the two places calls it. A caller has nothing of the rule to restate.
     */
    @Test
    void theRuleHasOneHome() {
        assertTrue(Compiler.compile(INJECTED).containsKey("demo.Fetch$Ensures"),
                "the module declaring the clause carries it");
        assertFalse(Compiler.compile(INJECTED).containsKey("demo.Use$Ensures"),
                "the module calling it declares no clause of its own");
    }

    /** A behavior stating nothing has no class and no call. */
    @Test
    void aBehaviorThatDeclaresNothingIsHeldNowhere() {
        Map<String, byte[]> classes = Compiler.compile("""
                module demo

                data Amount = Int

                behavior echo : (a: Amount) -> Amount
                let echo (a) = a
                """);

        assertFalse(classes.containsKey("demo.Echo$Ensures"));
        assertEquals(0, checksOf(classes.get("demo.Echo$Impl"), "demo/Echo$Ensures"));
    }
}
