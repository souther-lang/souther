package souther.compiler;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The two behaviors #963 was reported with, compiled together.
 *
 * <p>They say the same thing about the same list: a total of the amounts, constructed as a value
 * whose invariant is that it is at or above nought. One was written as a fold and read; the other
 * was written with the library's own {@code List.sum} and was a value nothing was known about. The
 * report this came from rewrote eleven such totals into folds and fifteen warnings went away, with
 * no change of meaning anywhere — the library being the expensive way to write something.
 *
 * <p>Three separate readings had to arrive for the second line to be read, and this is where they
 * meet: the primitive is made into the walk it means, what a {@code List.map} kept of the elements
 * it was built from travels to the walk that consumes them, and the range such a walk stays in is
 * proposed from what the step is handed. Each of those is held on its own elsewhere; what is held
 * here is that the model an author writes compiles clean.
 */
class TheSameTotalIsReadWhicheverWayItIsWrittenTest {

    @Test
    void aTotalWrittenAsAFoldAndOneWrittenWithTheLibraryAreBothRead() {
        Compiler.Compiled compiled = Compiler.compileWithWarnings("""
                module demo

                data U = Int
                    invariant nonNeg = value >= 0

                behavior a : (xs: List<U>) -> U
                    constructs U
                let a (xs) = U(List.fold((acc, x) -> acc + x.value, 0, xs))

                behavior b : (xs: List<U>) -> U
                    constructs U
                let b (xs) = U(List.sum(List.map(x -> x.value, xs)))
                """);
        assertEquals(List.of(), compiled.warnings().stream()
                        .filter(d -> d.severity() == Severity.WARNING)
                        .map(Diagnostic::code).toList(),
                "the two lines say the same thing about the same list");
    }
}
