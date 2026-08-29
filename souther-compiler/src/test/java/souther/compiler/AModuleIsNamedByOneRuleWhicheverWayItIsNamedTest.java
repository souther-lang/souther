package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;
import souther.compiler.jvm.ClassFileImage;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A module is named by one rule, whether the name was written or handed in.
 *
 * <p>A name in a source file is a name because the scan read it as one. A header-less source is
 * named after something nothing read — the stem of the file, or what an embedding passed to the
 * compiler — and it becomes the module's name all the same, so the same rule holds it. Left to
 * itself that entrance took anything at all: a module could be called `$x`, or `_foo`, or `a b`,
 * none of which a `module` header may write, and the name went on into the package the classes are
 * emitted under.
 */
class AModuleIsNamedByOneRuleWhicheverWayItIsNamedTest {

    private static final String HEADERLESS = """
            data In = { n: Int }
            data Out = Int

            behavior calc : (i: In) -> Out constructs Out

            let calc (i) = Out(i.n)
            """;

    @Test
    void aNameHandedInIsHeldToTheRuleAWrittenOneIsHeldTo() {
        for (String given : List.of("$x", "_foo", "my-module", "a b", "1st", "")) {
            CompileException refused = assertThrows(CompileException.class,
                    () -> Compiler.compile(HEADERLESS, given),
                    "`" + given + "` was taken as a module name");
            assertTrue(refused.getMessage().contains("E2301"),
                    "`" + given + "`: " + refused.getMessage());
        }
    }

    /** And the same spellings are refused where they are written, which is the rule being one. */
    @Test
    void andTheSameSpellingsAreRefusedInAHeader() {
        for (String written : List.of("$x", "_foo")) {
            assertThrows(CompileException.class,
                    () -> Compiler.compile("module " + written + "\n\n" + HEADERLESS),
                    "`module " + written + "` was read");
        }
    }

    /** The control: a name is still a name, in one part or several. */
    @Test
    void aNameThatIsOneIsTakenAsBefore() {
        emitsCalcUnder("demo");
        emitsCalcUnder("a.b");
        emitsCalcUnder("在庫");
    }

    /** The behavior lands in the package the module was named, whichever way it was named. */
    private static void emitsCalcUnder(String module) {
        Map<String, ClassFileImage> classes = Compiler.compile(HEADERLESS, module);
        assertTrue(classes.containsKey(Emitted.impl(module, "calc")), classes.keySet().toString());
    }
}
