package souther.compiler.check;

import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;
import souther.compiler.Compiler;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A value whose body calls a helper is accepted wherever it is named twice, whatever the two
 * regions are and whatever holds them.
 *
 * <p>The language accepts a program that names a value in two places. Each place that opens a
 * region is built for separately, and a call in the value's body is expanded once per build, so
 * what tells the expansions apart has to be in the owner of what they bind. A shape missing here is
 * a shape nobody has asked.
 */
class EveryPairOfRegionsANamedValueIsBuiltInIsAcceptedTest {

    private static final String HEAD = """
            module m exposing (f, g, Kind, Amount)

            data Kind = Yes | No

            data Amount = Int invariant value >= 0

            let same (n: Int) : Int = n

            let viaCall = same(List.length([1, 2, 3]))

            let bigger (m: Int) : Bool = m > viaCall

            """;

    /** A value the rules settle makes a branch on it dead, which says something about the program
     *  written here and nothing about what is asked. */
    private static final String DEAD_BRANCH = "E1327";

    /** Every region a value can be named in, each as a Bool that reads {@code viaCall}. */
    private static final List<String> REGIONS = List.of(
            "(if n > 0 then viaCall > 0 else false)",
            "(if n > 0 then false else viaCall > 0)",
            "(n > 0 && viaCall > 0)",
            "(n > 0 || viaCall > 0)",
            "(match k with | Yes -> viaCall > 0 | No -> false)",
            "(match k with | Yes -> false | No -> viaCall > 0)",
            "(if Amount(n) as a then viaCall > 0 else false)",
            "(if Amount(n) as a then false else viaCall > 0)",
            "(List.length([n | viaCall > 0, n > 0]) > 0)",
            "(List.length([viaCall | n > 0]) > 0)",
            "List.any(bigger, [n])",
            "(viaCall > 0)");

    /** Where the two regions are written. */
    private enum Holder {
        ONE_BEHAVIOR {
            @Override
            String around(String first, String second) {
                return """
                        behavior f : (n: Int, k: Kind) -> Bool
                        let f (n, k) = %s || %s

                        behavior g : (n: Int, k: Kind) -> Bool
                        let g (n, k) = true
                        """.formatted(first, second);
            }
        },
        TWO_BEHAVIORS {
            @Override
            String around(String first, String second) {
                return """
                        behavior f : (n: Int, k: Kind) -> Bool
                        let f (n, k) = %s

                        behavior g : (n: Int, k: Kind) -> Bool
                        let g (n, k) = %s
                        """.formatted(first, second);
            }
        },
        A_VALUE_NAMED_TWICE {
            @Override
            String around(String first, String second) {
                return """
                        behavior f : (n: Int, k: Kind) -> Bool
                        let f (n, k) = %s && %s

                        behavior g : (n: Int, k: Kind) -> Bool
                        let g (n, k) = (if n > 1 then %s else false) || %s
                        """.formatted(first, second, first, second);
            }
        };

        abstract String around(String first, String second);
    }

    @TestFactory
    Stream<DynamicTest> everyPairInEveryHolder() {
        List<DynamicTest> out = new ArrayList<>();
        for (Holder holder : Holder.values()) {
            for (String first : REGIONS) {
                for (String second : REGIONS) {
                    String source = HEAD + holder.around(first, second);
                    out.add(DynamicTest.dynamicTest(holder + " " + first + " / " + second,
                            () -> assertEquals(List.of(), Compiler.compiled(source, "m")
                                    .diagnostics().values().stream().flatMap(List::stream)
                                    .map(each -> each.diagnostic().code())
                                    .filter(code -> !DEAD_BRANCH.equals(code)).toList())));
                }
            }
        }
        return out.stream();
    }
}
