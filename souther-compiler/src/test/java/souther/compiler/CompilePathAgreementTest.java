package souther.compiler;

import souther.compiler.diag.Primary;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.params.provider.Arguments.arguments;

/**
 * One module compiles the same way whether it is compiled alone or linked with others. The two are
 * separate sequences over the same stages — {@code compiling} resolves against the module itself,
 * {@code linking} against every module's derived defs, and each has stages the other does not — so a
 * feature can work on one and not the other. That is what happened to the recursive prelude, which
 * the linking path did not inject, and every module that folded failed there with an NPE while the
 * single-module tests stayed green.
 *
 * <p>Nothing compared them. Each path had its own tests over its own inputs. This runs one source
 * through both and asserts they agree: the same classes on success, the same diagnostic on failure.
 * The annotation processor is not a third sequence — it calls one of these two — so covering both
 * covers what it runs.
 */
class CompilePathAgreementTest {

    /** Sources with no imports, so the single-module path accepts them, each exercising a form the
     *  two paths reach through different symbol tables. */
    static Stream<Arguments> sources() {
        return Stream.of(
                arguments("a newtype over a list", """
                        module demo exposing ( Tags )
                        data Tags = List<String>
                        """),
                arguments("a newtype over a map", """
                        module demo exposing ( Stock )
                        data Stock = Map<String, Int>
                        """),
                arguments("a newtype over a list of named data", """
                        module demo exposing ( Line, Lines )
                        data Line = { sku: String, qty: Int }
                        data Lines = List<Line>
                        """),
                arguments("a collection newtype carrying an invariant", """
                        module demo exposing ( Tags )
                        import List ( isEmpty )
                        data Tags = List<String>
                            invariant isEmpty(value) == false
                        """),
                arguments("an invariant whose pattern is composed", """
                        module demo exposing ( Postal )
                        let 接頭辞 = "[0-9]{3}"
                        data Postal = String
                            invariant String.matches(接頭辞 ++ "-[0-9]{4}", value)
                        """),
                arguments("a let opening a newtype", """
                        module demo exposing ( Tags, countTags )
                        import List ( length )
                        data Tags = List<String>

                        behavior countTags : (t: Tags) -> Int
                        let countTags (t) = {
                            let Tags(xs) = t
                            length(xs)
                        }
                        """),
                arguments("a helper parameter opening a newtype", """
                        module demo exposing ( Tags, countTags )
                        import List ( length )
                        data Tags = List<String>

                        let count (Tags(xs)) = length(xs)

                        behavior countTags : (t: Tags) -> Int
                        let countTags (t) = count(t)
                        """),
                arguments("a lambda parameter opening a record", """
                        module demo exposing ( Line, In, Out, quantities )
                        import List ( map )
                        data Line = { sku: String, qty: Int }
                        data In = { lines: List<Line> }
                        data Out = { qtys: List<Int> }

                        behavior quantities : (i: In) -> Out constructs Out
                        let quantities (i) = Out { qtys = map(({ qty }) -> qty, i.lines) }
                        """),
                arguments("a tuple destructure and a fold", """
                        module demo exposing ( In, Out, total )
                        import List ( fold )
                        data In = { xs: List<Int> }
                        data Out = { total: Int }

                        behavior total : (i: In) -> Out constructs Out
                        let total (i) = {
                            let (seed, _) = (0, 0)
                            Out { total = fold((acc, x) -> acc + x, seed, i.xs) }
                        }
                        """),
                arguments("an example over a collection newtype", """
                        module demo exposing ( Tags, countTags )
                        import List ( length )
                        data Tags = List<String>

                        behavior countTags : (t: Tags) -> Int
                        let countTags (t) = length(t.value)

                        example countTags
                          | (Tags(["a", "b"])) -> 2
                        """));
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("sources")
    void bothPathsProduceTheSameClasses(String name, String source) {
        Map<String, byte[]> alone = Compiler.compile(source);
        Map<String, byte[]> linked = Compiler.compileModules(List.of(source));
        assertEquals(alone.keySet(), linked.keySet(),
                "the two paths emit different classes for " + name);
    }

    /** Sources with no imports whose error both paths must report the same way. */
    static Stream<Arguments> brokenSources() {
        return Stream.of(
                arguments("a tuple as a newtype base", """
                        module demo
                        data Pair = (String, Int)
                        """),
                arguments("an optional as a newtype base", """
                        module demo
                        data Note = String?
                        """),
                arguments("a map newtype keyed off the boundary", """
                        module demo
                        data Stock = Map<Int, Int>
                        """),
                arguments("opening something that is not a newtype", """
                        module demo
                        data Line = { sku: String, qty: Int }
                        data Out = { v: String }

                        behavior read : (l: Line) -> Out constructs Out
                        let read (l) = {
                            let Line(x) = l
                            Out { v = x }
                        }
                        """),
                arguments("opening a newtype the value is not", """
                        module demo
                        data Tags = List<String>
                        data Labels = List<String>
                        data Out = { v: Int }

                        behavior read : (t: Tags) -> Out constructs Out
                        let read (t) = {
                            let Labels(xs) = t
                            Out { v = 1 }
                        }
                        """));
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("brokenSources")
    void bothPathsReportTheSameDiagnostic(String name, String source) {
        CompileException alone = compileError(() -> Compiler.compile(source));
        CompileException linked = compileError(() -> Compiler.compileModules(List.of(source)));
        assertEquals(alone.diagnostic().said(), linked.diagnostic().said(),
                "the two paths disagree on what is wrong with " + name);
        assertEquals(((Primary.InSource) alone.diagnostic().primary()).place().region().start(), ((Primary.InSource) linked.diagnostic().primary()).place().region().start(),
                "the two paths disagree on where " + name + " is wrong");
    }

    private static CompileException compileError(Runnable compile) {
        try {
            compile.run();
        } catch (CompileException e) {
            return e;
        }
        throw new AssertionError("expected a compile error, but the source compiled");
    }
}
