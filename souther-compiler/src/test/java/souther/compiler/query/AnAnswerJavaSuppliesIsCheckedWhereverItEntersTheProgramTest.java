package souther.compiler.query;

import souther.compiler.Compiler;
import souther.compiler.core.EnsuresEnforcement;
import souther.compiler.diag.CompileException;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;
import souther.compiler.program.CheckedProgram;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassFile;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a behavior declares of its answer is checked where that answer enters the program, in
 * whichever module the entry is.
 *
 * <p>An answer Java supplies enters at each call, and a caller in another module may assume what the
 * behavior declares of it as a caller in its own module may. So every class calling it checks it,
 * with the check the declaring module emitted, read off the behavior's projection. A behavior with a
 * body checks its own answer, and no caller checks it again.
 *
 * <p>The projection is what an artifact records of the behavior, so a module built calling a check
 * that the module it was built against has since dropped is refused where it is read, as any other
 * way of linking that moved is.
 */
class AnAnswerJavaSuppliesIsCheckedWhereverItEntersTheProgramTest {

    private static final String CLAUSE = "    ensures doubled = value.value == a.value * 2\n";

    private static final String DECLARING = """
            module up exposing ( Amount, fetch )

            data Amount = Int

            behavior fetch : (a: Amount) -> Amount
            """ + CLAUSE;

    private static final String CALLING = """
            module down exposing ( use, inc )

            import up ( Amount, fetch )

            behavior use : (a: Amount) -> Amount
                depends on fetch
            let use (a, fetch) = fetch(a)

            behavior inc : (n: Int) -> Int
            let inc (n) = n + 1
            """;

    /** How many times {@code classBytes} calls {@code owner}'s {@code check}, over every method it
     *  has. The owner is counted, so a call to some other behavior's check is not read as this one. */
    private static int checksOf(ClassFileImage image, String owner) {
        int[] found = {0};
        ClassFile.of().parse(image.bytes()).methods()
                .forEach(m -> m.code().ifPresent(code -> code.forEach(e -> {
                    if (e instanceof InvokeInstruction inv
                            && inv.name().stringValue().equals("check")
                            && inv.owner().name().stringValue().equals(owner)) {
                        found[0]++;
                    }
                })));
        return found[0];
    }

    @Test
    void theDeclaringModuleCarriesTheCheck() {
        Map<String, ClassFileImage> classes = Compiler.compileModules(List.of(DECLARING, CALLING));

        assertTrue(classes.containsKey("up.Fetch$Ensures"),
                "the clause is `up`'s, so the class holding it is: " + classes.keySet());
    }

    @Test
    void aCallerInAnotherModuleChecksAnAnswerJavaSupplies() {
        Map<String, ClassFileImage> classes = Compiler.compileModules(List.of(DECLARING, CALLING));

        assertEquals(1, checksOf(classes.get("down.Use$Impl"), "up/Fetch$Ensures"));
    }

    /** And one compiled against the declaring module's published classes. */
    @Test
    void aCallerBuiltAgainstTheDeclaringModuleOffThePathChecksIt() {
        Map<String, ClassFileImage> classes = Compiler.compileModules(List.of(CALLING),
                ModulePath.of(Compiler.compile(DECLARING)));

        assertEquals(1, checksOf(classes.get("down.Use$Impl"), "up/Fetch$Ensures"));
    }

    /**
     * And an output reading the checked program is told so of the same behavior: the target a call
     * reaches says where its clause is checked, for a module read off the path as for one compiled
     * here.
     */
    @Test
    void theProgramSaysACallerChecksIt() {
        CheckedProgram program = CheckedProgram.of(List.of(CALLING),
                ModulePath.of(Compiler.compile(DECLARING)));

        assertInstanceOf(EnsuresEnforcement.AtEachCrossing.class,
                program.behavior(new ValueName.Behavior("up", "fetch")).ensures());
    }

    /** A body checks its own answer, so no caller in any module checks it again. */
    @Test
    void aCallerChecksNothingABodyChecksItself() {
        Map<String, ClassFileImage> classes = Compiler.compileModules(List.of(DECLARING
                + "    constructs Amount\nlet fetch (a) = Amount { value = a.value * 2 }\n",
                CALLING.replace("    depends on fetch\nlet use (a, fetch) = fetch(a)",
                        "let use (a) = fetch(a)")));

        assertEquals(0, checksOf(classes.get("down.Use$Impl"), "up/Fetch$Ensures"));
    }

    /**
     * `down`, built calling `up`'s check, read off the path beside an `up` that no longer declares
     * the clause: the check it calls is gone, and a compile reading `down` is refused for it —
     * whatever of `down` it uses.
     */
    @Test
    void aModuleBuiltCallingACheckItsDependencyDroppedIsRefused() {
        Map<String, ClassFileImage> path = new HashMap<>(Compiler.compileModules(List.of(CALLING),
                ModulePath.of(Compiler.compile(DECLARING))));
        path.putAll(Compiler.compile(DECLARING.replace(CLAUSE, "")));

        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module app
                        import down ( inc )
                        behavior twice : (n: Int) -> Int
                        let twice (n) = inc(inc(n))
                        """), ModulePath.of(path)));
        assertEquals("E1510", refused.diagnostic().code(), refused.getMessage());
        assertTrue(refused.getMessage().contains("checked where called by"), refused.getMessage());
    }
}
