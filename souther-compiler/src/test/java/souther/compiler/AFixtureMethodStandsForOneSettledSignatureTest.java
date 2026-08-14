package souther.compiler;

import souther.compiler.diag.CompileException;
import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassFile;
import java.lang.classfile.MethodModel;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a method emitted for a fixture's call stands for is the signature that call settled — not the
 * call, and not the row it was written in.
 *
 * <p>Two rows settling one signature apply one method, and two signatures are two methods however
 * they were arrived at. Both halves are here because either one alone is satisfied by a name that
 * is wrong in the other direction: naming per call site passes the first, and one name per kernel
 * passes the second.
 */
class AFixtureMethodStandsForOneSettledSignatureTest {

    /** The methods any emitted class carries whose name begins with {@code prefix}. Read off the
     *  bytecode, so what is counted is what a row would reach. */
    private static Set<String> methodsNamed(Map<String, byte[]> classes, String prefix) {
        Set<String> found = new LinkedHashSet<>();
        for (byte[] bytes : classes.values()) {
            for (MethodModel method : ClassFile.of().parse(bytes).methods()) {
                String name = method.methodName().stringValue();
                if (name.startsWith(prefix)) {
                    found.add(name);
                }
            }
        }
        return found;
    }

    @Test
    void twoInstancesOfOneKernelAreTwoMethods() {
        Map<String, byte[]> classes = Compiler.compile("""
                module demo

                data Amount = Int
                data Weight = Decimal

                behavior billed : (a: Amount) -> Amount

                let billed (a) = a

                behavior weighed : (w: Weight) -> Weight

                let weighed (w) = w

                example billed
                  | (Amount(List.sum([ 1, 2 ]))) -> Amount(3)

                example weighed
                  | (Weight(List.sum([ 1.5m, 2.5m ]))) -> Weight(4.0m)
                """);
        assertEquals(2, methodsNamed(classes, "$intrinsic$List$sum").size(),
                "summing Int and summing Decimal are two instances: " + methodsNamed(classes, "$intrinsic$List$sum"));
    }

    @Test
    void oneInstanceReachedFromTwoRowsIsOneMethod() {
        Map<String, byte[]> classes = Compiler.compile("""
                module demo

                data Amount = Int

                behavior billed : (a: Amount) -> Amount

                let billed (a) = a

                example billed
                  | (Amount(List.length([ 1, 2 ]))) -> Amount(2)
                  | (Amount(List.length([ 7 ]))) -> Amount(1)
                """);
        assertEquals(1, methodsNamed(classes, "$intrinsic$List$length").size(),
                "both rows settled List<Int>, which is one instance: "
                        + methodsNamed(classes, "$intrinsic$List$length"));
    }

    /**
     * Why a helper written in Souther is reached through the method it already has, rather than
     * through one emitted per instance.
     *
     * <p>A kernel's lowering may read the type it is applied at, and a method emitted at a
     * declaration's own signature has nothing for it to read. That cannot happen inside a Souther
     * body: a body that carries an open variable into such a kernel is refused where it is written,
     * so the method a module emits for a polymorphic helper never has that choice to make. This is
     * the measurement that reason rests on, and it is here so that a change to it is a change to a
     * test rather than a fixture that answers a wrong number.
     */
    @Test
    void aHelperCannotCarryAnOpenVariableIntoAKernelThatChoosesByType() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Amount = Int

                let total (xs) = List.sum(xs)

                behavior billed : (a: Amount) -> Amount

                let billed (a) = a
                """));
        assertTrue(e.getMessage().contains("E1817"), e.getMessage());
    }
}
