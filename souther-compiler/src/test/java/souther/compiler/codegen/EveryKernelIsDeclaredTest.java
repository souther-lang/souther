package souther.compiler.codegen;

import souther.compiler.Prelude;
import souther.compiler.ast.Ast;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every kernel the library ships is described by a declaration (ADR-0053). The signature lives in a
 * core module and the compiler holds only what a declaration cannot say — a kind, an ordering, the
 * branch a partial division emits.
 *
 * <p>Asked as a correspondence rather than as "the table of signatures is empty": an emitter added
 * without a declaration is a function that can be called and whose type nothing states, which is
 * what the table of signatures was.
 */
class EveryKernelIsDeclaredTest {

    @Test
    void everyEmittedKernelHasADeclarationNamingIt() {
        Set<String> emittedWithNoDeclaration = new LinkedHashSet<>(Intrinsics.keys());
        emittedWithNoDeclaration.removeAll(declaredKeys());

        assertEquals(Set.of(), emittedWithNoDeclaration,
                "a kernel is emitted that no declaration describes");
    }

    @Test
    void everyDeclaredKernelHasAnEmitterOrIsWrittenOutInTheBackend() {
        // The three partial divisions answer a case rather than a number when the divisor is zero,
        // so they emit a branch and are written out in BodyGen rather than held as a table row.
        Set<String> writtenOut = Set.of("int.divide", "int.truncatingRemainder", "decimal.divide");

        Set<String> declaredWithNoEmitter = new LinkedHashSet<>();
        for (String key : declaredKeys()) {
            if (!Intrinsics.keys().contains(key) && !writtenOut.contains(key)) {
                declaredWithNoEmitter.add(key);
            }
        }

        assertEquals(Set.of(), declaredWithNoEmitter,
                "a kernel is declared that nothing emits");
    }

    /** The kernel keys the library's declarations name: the entries whose body is a kernel. */
    private static Set<String> declaredKeys() {
        Set<String> declared = new LinkedHashSet<>();
        for (Prelude.PreludeEntry entry : Prelude.entries().values()) {
            if (entry.declaration().body() instanceof Ast.FnBody.Intrinsic kernel) {
                declared.add(kernel.key());
            }
        }
        return declared;
    }
}
