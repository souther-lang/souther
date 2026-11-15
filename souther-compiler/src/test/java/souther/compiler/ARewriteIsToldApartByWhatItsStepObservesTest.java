package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A rewrite is told apart within the runs it is given by a candidate that changes what the walk's
 * step observes, ahead of one that changes what no step observes.
 */
class ARewriteIsToldApartByWhatItsStepObservesTest {

    /** Every row answers alike, so what the rows answered says nothing of where the step differs. */
    @Test
    void aValueTheStepComparesIsReachedWhenEveryRowAnsweredAlike() {
        StringBuilder cases = new StringBuilder();
        StringBuilder arms = new StringBuilder();
        StringBuilder rows = new StringBuilder();
        for (char each = 'A'; each <= 'Z'; each++) {
            cases.append(each).append(each < 'Z' ? " | " : "");
            arms.append("        | ").append(each).append(" -> ").append(each == 'Z').append('\n');
            rows.append("    | \"").append(each).append("\" : ([ ").append(each)
                    .append(" ]) -> false\n");
        }
        String source = "module repro.observed\n\ndata Payer = " + cases + "\n\n"
                + "let isZ (p: Payer): Bool =\n    match p with\n" + arms + "\n"
                + "behavior check : (ls: List<Payer>) -> Bool\n"
                + "let check (ls) = List.length(ls) >= 2 && List.any(p -> isZ(p), ls)\n\n"
                + "example check\n" + rows;

        assertEquals(List.of(), undecided(measured(source)));
    }

    /**
     * The number the step compares an element with is in no row, so nothing the rows hold reaches
     * it: it is a border of the step, which the step is what says.
     */
    @Test
    void aNumberOnlyTheStepComparesIsReached() {
        String source = """
                module repro.border

                behavior check : (xs: List<Int>) -> Bool
                let check (xs) = List.length(xs) >= 2 && List.any(x -> x > 1000, xs)

                example check
                    | "none" : ([ ]) -> false
                    | "one" : ([ 1 ]) -> false
                    | "two" : ([ 1, 2 ]) -> false
                    | "three" : ([ 5, 6, 7 ]) -> false
                """;

        assertEquals(List.of(), undecided(measured(source)));
    }

    private static final String STOCK_WITH_MANY_NUMBERS = """
            module repro.stock

            data Stock = { sku: String, qty: Int }

            behavior readStock : (sku: String) -> List<Stock>

            behavior available : (sku: String, want: Int, a: Int, b: Int, c: Int, d: Int) -> Bool
                depends on readStock

            let available (sku, want, a, b, c, d, readStock) = {
                let found = List.indexBy(.sku, readStock(sku))
                    |> Map.get(sku)
                    |> Option.map(s -> s.qty >= want)
                    |> Option.withDefault(false)
                found && (a > 10 || b > 20 || c > 30 || d > 40 || a < -10 || b < -20 || c < -30 || d < -40)
            }

            fake readStock
                | _ -> [ Stock { sku = "apple", qty = 3 } ]

            example available
                | "enough" : ("apple", 2, 50, 0, 0, 0) -> true
                | "too many" : ("apple", 5, 50, 0, 0, 0) -> false
                | "unknown" : ("pear", 1, 50, 0, 0, 0) -> false
                | "small" : ("apple", 1, 0, 0, 0, 0) -> false
            """;

    /** Many comparisons of numbers the walk never reads must not use the runs the answer needs. */
    @Test
    void aDependencysAnswerIsGrownWhereTheInputsHaveManyClasses() {
        assertEquals(List.of(), undecided(measured(STOCK_WITH_MANY_NUMBERS)));
    }

    /** The walk itself reads many numbers, so the classes of those are many as well. */
    @Test
    void aWalkThatReadsManyNumbersIsDecidedAsOneThatReadsFew() {
        String source = """
                module repro.reading

                data Stock = { sku: String, qty: Int }

                behavior readStock : (sku: String) -> List<Stock>

                behavior available : (sku: String, want: Int, a: Int, b: Int, c: Int, d: Int) -> Bool
                    depends on readStock

                let available (sku, want, a, b, c, d, readStock) =
                    List.indexBy(.sku, List.filter(s -> s.qty > a || s.qty > b || s.qty > c || s.qty > d, readStock(sku)))
                        |> Map.get(sku)
                        |> Option.map(s -> s.qty >= want)
                        |> Option.withDefault(false)

                fake readStock
                    | _ -> [ Stock { sku = "apple", qty = 3 } ]

                example available
                    | "enough" : ("apple", 2, 0, 0, 0, 0) -> true
                    | "too many" : ("apple", 5, 0, 0, 0, 0) -> false
                    | "unknown" : ("pear", 1, 0, 0, 0, 0) -> false
                """;

        assertEquals(List.of(), undecided(measured(source)));
    }

    private static List<String> undecided(Compilation compilation) {
        return page(compilation).lines().map(String::strip)
                .filter(line -> line.startsWith("? not decided whether a row would come out"))
                .toList();
    }

    private static String page(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        return ACompiledModel.compiles(compilation);
    }
}
