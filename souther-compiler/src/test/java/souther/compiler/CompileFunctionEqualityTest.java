package souther.compiler;

import souther.compiler.diag.msg.TypeMessage;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Two functions are not equal or unequal: {@code ==} is value equality (ADR-0009), and a function
 * value has no value to compare. Refused where the comparison is written rather than left to
 * compare object identity at run time, and refused the same way where a {@code Set} or a
 * {@code Map} would ask the same question of an element or a key.
 */
class CompileFunctionEqualityTest {

    private static Diagnostic diagnosticOf(String src) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        return e.diagnostic();
    }

    @Test
    void twoFunctionsCannotBeCompared() {
        Diagnostic d = diagnosticOf("""
                module demo
                data R = { same: Bool }
                behavior run : (n: Int) -> R
                    constructs R
                let run (n) = {
                    let p: (Int) -> Bool = (x) -> x > n
                    let q: (Int) -> Bool = (x) -> x > n
                    R { same = p == q }
                }
                """);
        assertInstanceOf(TypeMessage.AFunctionHasNoValueToCompare.class, d.said());
    }

    @Test
    void aSetCannotHoldFunctions() {
        Diagnostic d = diagnosticOf("""
                module demo
                data R = { n: Int }
                behavior run : (n: Int) -> R
                    constructs R
                let run (n) = {
                    let p: (Int) -> Bool = (x) -> x > n
                    let s: Set<(Int) -> Bool> = Set.singleton(p)
                    R { n = Set.size(s) }
                }
                """);
        assertInstanceOf(TypeMessage.ASetElementIsComparedAndAFunctionIsNot.class, d.said());
    }

    @Test
    void aMapCannotBeKeyedByAFunction() {
        Diagnostic d = diagnosticOf("""
                module demo
                data R = { n: Int }
                behavior run : (n: Int) -> R
                    constructs R
                let run (n) = {
                    let p: (Int) -> Bool = (x) -> x > n
                    let m: Map<(Int) -> Bool, Int> = Map.singleton(p, 1)
                    R { n = Map.size(m) }
                }
                """);
        assertInstanceOf(TypeMessage.AMapKeyIsComparedAndAFunctionIsNot.class, d.said());
    }

    // The set `distinct` grows to remember what it has seen is never written down, so only the
    // elaborated type says what its elements are.
    @Test
    void aCollectionTheCheckerInfersIsAskedTheSameQuestion() {
        Diagnostic d = diagnosticOf("""
                module demo
                data R = { n: Int }
                behavior run : (n: Int) -> R
                    constructs R
                let run (n) = {
                    let f: (Int) -> Bool = (x) -> x > n
                    let fs: List<(Int) -> Bool> = [f, f]
                    R { n = List.length(List.distinct(fs)) }
                }
                """);
        assertInstanceOf(TypeMessage.ASetElementIsComparedAndAFunctionIsNot.class, d.said());
    }

    // A Set asks whether two elements are equal and a Map whether two keys are. Those are different
    // requirements, so a map the checker inferred is not reported as a set.
    @Test
    void aMapTheCheckerInfersIsReportedAsAMap() {
        Diagnostic d = diagnosticOf("""
                module demo
                data R = { n: Int }
                behavior run : (v: Int) -> R
                    constructs R
                let run (v) = {
                    let p: (Int) -> Bool = (x) -> x > v
                    R { n = Map.size(Map.singleton(p, 1)) }
                }
                """);
        assertInstanceOf(TypeMessage.AMapKeyIsComparedAndAFunctionIsNot.class, d.said());
    }

    @Test
    void aMapGroupedByAFunctionKeyIsReportedAsAMap() {
        Diagnostic d = diagnosticOf("""
                module demo
                data Item = { a: Int }
                data R = { n: Int }
                behavior run : (xs: List<Item>, v: Int) -> R
                    constructs R
                let run (xs, v) = {
                    let p: (Int) -> Bool = (x) -> x > v
                    R { n = Map.size(List.groupBy((i) -> p, xs)) }
                }
                """);
        assertInstanceOf(TypeMessage.AMapKeyIsComparedAndAFunctionIsNot.class, d.said());
    }
}
