package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

/**
 * A rewrite is told apart within the runs it is given by a candidate that changes what the walk's
 * step observes, ahead of one that changes what no step observes.
 *
 * <p>Each reads what the model owes of the walk's rewrites ({@link WalkRewritesOwed}): a page with
 * nothing undecided on it is also the page of a rewrite never owed.
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
        // One row of two payers, so that the walk is entered at all: a list of one is not walked.
        rows.append("    | \"AB\" : ([ A, B ]) -> false\n");
        String source = "module repro.observed\n\ndata Payer = " + cases + "\n\n"
                + "let isZ (p: Payer): Bool =\n    match p with\n" + arms + "\n"
                + "behavior check : (ls: List<Payer>) -> Bool\n"
                + "let check (ls) = List.length(ls) >= 2 && List.any(p -> isZ(p), ls)\n\n"
                + "example check\n" + rows;

        assertToldApart(measured(source), "any");
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

        assertToldApart(measured(source), "any");
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
        assertToldApart(measured(STOCK_WITH_MANY_NUMBERS), "indexBy");
    }

    /**
     * A number only the step compares an element with, on the negative side: written as a
     * negation of a literal, which is a border all the same.
     */
    @Test
    void aNegativeNumberOnlyTheStepComparesIsReached() {
        String source = """
                module repro.negative

                behavior check : (xs: List<Int>) -> Bool
                let check (xs) = List.length(xs) >= 2 && List.any(x -> x == -100000, xs)

                example check
                    | "none" : ([ ]) -> false
                    | "one" : ([ 1 ]) -> false
                    | "two" : ([ 1, 2 ]) -> false
                    | "three" : ([ 5, 6, 7 ]) -> false
                """;

        assertToldApart(measured(source), "any");
    }

    /**
     * Many dependencies answer lists, and the walk goes over what only the last of them answers:
     * the answers of the others are not what it observes, and a candidate that changes them takes
     * the runs of the one that does.
     */
    @Test
    void theAnswerOfTheDependencyTheWalkReadsIsGrownAmongManyItDoesNot() {
        StringBuilder behaviors = new StringBuilder();
        StringBuilder depends = new StringBuilder();
        StringBuilder names = new StringBuilder();
        StringBuilder sums = new StringBuilder();
        StringBuilder fakes = new StringBuilder();
        for (int at = 1; at <= 10; at++) {
            behaviors.append("behavior u").append(at).append(" : (k: String) -> List<Int>\n");
            depends.append("    depends on u").append(at).append('\n');
            names.append("u").append(at).append(", ");
            sums.append(" + List.length(u").append(at).append("(sku))");
            fakes.append("fake u").append(at).append("\n    | _ -> [ 1 ]\n\n");
        }
        String source = """
                module repro.many

                data Stock = { sku: String, qty: Int }

                %sbehavior readStock : (sku: String) -> List<Stock>

                behavior available : (sku: String, want: Int) -> Int
                %s    depends on readStock

                let available (sku, want, %sreadStock) = {
                    let found = List.indexBy(.sku, readStock(sku))
                        |> Map.get(sku)
                        |> Option.map(s -> s.qty >= want)
                        |> Option.withDefault(false)
                    if found then 0%s else 99
                }

                %sfake readStock
                    | _ -> [ Stock { sku = "apple", qty = 3 } ]

                example available
                    | "enough" : ("apple", 2) -> 10
                    | "too many" : ("apple", 5) -> 99
                    | "unknown" : ("pear", 1) -> 99
                """.formatted(behaviors, depends, names, sums, fakes);

        assertToldApart(measured(source), "indexBy");
    }

    /**
     * Many lists are handed in, and the walk goes over the last: growing the others changes
     * nothing it observes. Decided with or without the others left alone, so it holds the walk
     * over the list it reads and does not say the others cost anything.
     */
    @Test
    void theListTheWalkGoesOverIsGrownAmongManyItDoesNot() {
        StringBuilder parameters = new StringBuilder();
        StringBuilder names = new StringBuilder();
        StringBuilder lengths = new StringBuilder("0");
        StringBuilder others = new StringBuilder();
        for (int at = 1; at <= 8; at++) {
            parameters.append("l").append(at).append(": List<Int>, ");
            names.append("l").append(at).append(", ");
            lengths.append(" + List.length(l").append(at).append(")");
            others.append("[ 1 ], ");
        }
        String source = """
                module repro.lists

                behavior check : (%sxs: List<Int>) -> Bool
                let check (%sxs) = %s >= 0 && List.length(xs) >= 2 && List.any(x -> x > 1000, xs)

                example check
                    | "none" : (%s[ ]) -> false
                    | "one" : (%s[ 1 ]) -> false
                    | "two" : (%s[ 1, 2 ]) -> false
                """.formatted(parameters, names, lengths, others, others, others);

        assertToldApart(measured(source), "any");
    }

    /** The side of a negative border the difference lies on is either: here it is the one below. */
    @Test
    void aNegativeBorderIsToldApartFromEitherSide() {
        String source = """
                module repro.below

                behavior check : (xs: List<Int>) -> Bool
                let check (xs) = List.length(xs) >= 2 && List.any(x -> x < -100000, xs)

                example check
                    | "none" : ([ ]) -> false
                    | "one" : ([ 1 ]) -> false
                    | "two" : ([ 1, 2 ]) -> false
                    | "three" : ([ 5, 6, 7 ]) -> false
                """;

        assertToldApart(measured(source), "any");
    }

    /**
     * A number the walk reads, through what it asks a dependency for, is compared in many places,
     * so its classes are many, and the rows that fill each of them tell the rewrite nothing: a
     * search of those classes must not take the runs the answer a dependency gives needs.
     */
    @Test
    void manyClassesThatTellNothingApartDoNotTakeTheRunsOfTheAnswer() {
        StringBuilder forks = new StringBuilder();
        for (int at = 1; at <= 12; at++) {
            forks.append("    let f").append(at).append(" = if n > ").append(at * 10)
                    .append(" then 1 else 0\n");
        }
        for (char other = 'a'; other <= 'f'; other++) {
            forks.append("    let g").append(other).append(" = if ").append(other)
                    .append(" > 10 then 1 else 0\n");
        }
        String source = """
                module repro.hogging

                data Stock = { sku: String, qty: Int }

                behavior readStock : (sku: String, n: Int) -> List<Stock>

                behavior available : (sku: String, want: Int, n: Int, a: Int, b: Int, c: Int, d: Int, e: Int, f: Int) -> Int
                    depends on readStock

                let available (sku, want, n, a, b, c, d, e, f, readStock) = {
                %s    let found = List.indexBy(.sku, readStock(sku, n))
                        |> Map.get(sku)
                        |> Option.map(s -> s.qty >= want)
                        |> Option.withDefault(false)
                    if found then f1 + f2 + f3 + f4 + f5 + f6 + f7 + f8 + f9 + f10 + f11 + f12 + ga + gb + gc + gd + ge + gf else 99
                }

                fake readStock
                    | _ -> [ Stock { sku = "apple", qty = 3 } ]

                example available
                    | "enough" : ("apple", 2, 0, 0, 0, 0, 0, 0, 0) -> 0
                    | "too many" : ("apple", 5, 0, 0, 0, 0, 0, 0, 0) -> 99
                    | "unknown" : ("pear", 1, 0, 0, 0, 0, 0, 0, 0) -> 99
                """.formatted(forks);

        assertToldApart(measured(source), "indexBy");
    }

    private static void assertToldApart(Compilation compilation, String walk) {
        WalkRewritesOwed.assertToldApart(compilation, walk);
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

        assertToldApart(measured(source), "indexBy");
        assertToldApart(measured(source), "filter");
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        return ACompiledModel.compiles(compilation);
    }
}
