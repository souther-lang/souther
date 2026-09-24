package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.check.InvariantChecker.Said;
import souther.compiler.check.InvariantChecker.Verdict;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A case split written twice is one value wherever each writing stands, and two splits of the same
 * shape over different values are two.
 *
 * <p>A guard over a split and a construction over the same split are read together: the arm the
 * guard settled is the arm the construction is built from. Which writings are the same split is
 * asked of their keys, and a key is read in the environment its split stands in — a helper called
 * twice is two bindings of one argument, so each call's split is read with its own binding entered.
 *
 * <p>The condition is a choice between two comparisons, which the facts take nothing from, so what
 * the guard settles reaches the construction only through the split being the same one.
 */
class ASplitIsKeyedWhereItStandsTest {

    private static final String TYPES = """
            module m
            data No
            data Pos = Int
                invariant value > 0
            let sign (x: Int): Int = if x * x > 4 || x > 100 then 1 else 0 - 1
            behavior f : (n: Int) -> Pos | No
                constructs Pos
            """;

    /** The guard and the construction, each written as a helper call or as the split itself. */
    @ParameterizedTest(name = "{0}")
    @ValueSource(strings = {
            // each call is a binding of its own
            """
            let f (n) = {
                guard sign(n) > 0 else No
                Pos { value = sign(n) }
            }""",
            // the argument named first, and each call a binding of the name
            """
            let f (n) = {
                let t = n
                guard sign(t) > 0 else No
                Pos { value = sign(t) }
            }""",
            // one call, and the guard written out
            """
            let f (n) = {
                guard (if n * n > 4 || n > 100 then 1 else 0 - 1) > 0 else No
                Pos { value = sign(n) }
            }""",
            // both written out, where no binding stands between them
            """
            let f (n) = {
                guard (if n * n > 4 || n > 100 then 1 else 0 - 1) > 0 else No
                Pos { value = if n * n > 4 || n > 100 then 1 else 0 - 1 }
            }"""})
    void theGuardSettlesTheSplitTheConstructionIsBuiltFrom(String body) {
        assertEquals(List.of(Verdict.PROVED), verdicts(TYPES + body));
    }

    /** Two names bound to different values, and a split of each with the same shape. */
    @Test
    void aSplitOfAnotherValueIsNotSettledByTheGuard() {
        assertEquals(List.of(Verdict.UNKNOWN), verdicts(TYPES + """
                let f (n) = {
                    let a = n
                    let b = n + 1
                    guard sign(a) > 0 else No
                    Pos { value = sign(b) }
                }"""));
    }

    private static List<Verdict> verdicts(String source) {
        List<Said> said = Collections.synchronizedList(new ArrayList<>());
        InvariantChecker.WATCHING = said;
        try {
            Compiler.compileWithWarnings(source);
        } finally {
            InvariantChecker.WATCHING = null;
        }
        return said.stream().filter(s -> s.type().endsWith("Pos")).map(Said::verdict).toList();
    }
}
