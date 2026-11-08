package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.diag.Located;
import souther.compiler.diag.Severity;
import souther.compiler.query.Compilation;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.OperationLaw;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A guard written in terms of a library operation settles, for the discharge of a rule, what the
 * operation's law says it settles: some element meeting a statement, how many do, how many
 * different values the elements come to, how many they hold added up, how many code points of a
 * string are in a class, and a string standing inside another.
 *
 * <p>Each row is a body under a {@code Digit} whose invariant is {@code value >= 0}, and says
 * whether the discharge owes it anything. A row owed nothing is what the law settles; the row
 * beside it moves the number by one, asks of another closure, drops the guard or reads the other
 * side of it, and is owed — so neither side passes by proving, or by refusing, everything.
 */
class AGuardOverALibraryOperationSettlesWhatItsLawSaysTest {

    /** A body of {@code f}, and whether the discharge leaves anything owed of it. */
    private record Row(String body, boolean owed) {}

    private static final List<Row> ROWS = List.of(
            // Some element meeting what a closure answers is how many meet it being above nought,
            // and what a filter by the same closure holds is that number.
            new Row("if List.any(n -> n > 2, xs) then "
                    + "Digit(List.length(List.filter(n -> n > 2, xs)) - 1) else Digit(0)", false),
            new Row("if List.any(n -> n > 2, xs) then "
                    + "Digit(List.length(List.filter(n -> n > 2, xs)) - 2) else Digit(0)", true),
            new Row("if List.any(n -> n > 2, xs) then "
                    + "Digit(List.length(List.filter(n -> n > 3, xs)) - 1) else Digit(0)", true),
            new Row("if List.any(n -> n > 2, xs) then Digit(0) "
                    + "else Digit(0 - List.length(List.filter(n -> n > 2, xs)))", false),
            new Row("if List.any(n -> n > 2, xs) then Digit(List.length(xs) - 1) else Digit(0)",
                    false),
            new Row("if List.any(n -> n > 2, xs) then Digit(List.length(xs) - 2) else Digit(0)",
                    true),
            // Every element meeting it is none failing it: as many meet it as there are.
            new Row("if List.all(n -> n > 2, xs) && List.length(xs) >= 1 then "
                    + "Digit(List.length(List.filter(n -> n > 2, xs)) - 1) else Digit(0)", false),
            new Row("if List.all(n -> n > 2, xs) then "
                    + "Digit(List.length(List.filter(n -> n > 2, xs)) - 1) else Digit(0)", true),
            // Some element being the value is how many are, which is no more than there are.
            new Row("if List.contains(x, xs) then Digit(List.length(xs) - 1) else Digit(0)", false),
            new Row("if List.contains(x, xs) then Digit(List.length(xs) - 2) else Digit(0)", true),
            new Row("if Set.contains(x, a) then Digit(Set.size(a) - 1) else Digit(0)", false),
            // How many the elements hold added up: what was written out, or the sum of a list of
            // lists, which holds no fewer than how many of them hold something.
            new Row("if List.length(xs) >= 1 then "
                    + "Digit(List.length(List.concat([xs, xs])) - 2) else Digit(0)", false),
            new Row("if List.length(xs) >= 1 then "
                    + "Digit(List.length(List.concat([xs, xs])) - 3) else Digit(0)", true),
            new Row("if List.length(List.concat(xss)) >= 1 then "
                    + "Digit(List.length(xss) - 1) else Digit(0)", false),
            new Row("if List.length(List.concat(xss)) >= 1 then "
                    + "Digit(List.length(xss) - 2) else Digit(0)", true),
            // How many different values the elements come to is no more than there are, and the
            // same number however it is asked for.
            new Row("Digit(List.length(xs) - Set.size(Set.fromList(xs)))", false),
            new Row("Digit(Set.size(Set.fromList(xs)) - List.length(xs))", true),
            new Row("Digit(Set.size(Set.fromList(xs)) - List.length(List.distinct(xs)))", false),
            new Row("Digit(Set.size(Set.fromList(xs)) - List.length(List.distinct(xs)) - 1)",
                    true),
            new Row("if List.allDistinctBy(n -> n, xs) then "
                    + "Digit(List.length(List.distinctBy(n -> n, xs)) - List.length(xs)) "
                    + "else Digit(0)", false),
            new Row("Digit(List.length(List.distinctBy(n -> n, xs)) - List.length(xs))", true),
            new Row("if List.length(xs) >= 1 then "
                    + "Digit(Map.size(List.groupBy(n -> n, xs)) - 1) else Digit(0)", false),
            // How many code points are not whitespace is no more than the string holds, read
            // either way from what a trim holds.
            new Row("if String.length(String.trim(s)) >= 1 then "
                    + "Digit(String.length(s) - 1) else Digit(0)", false),
            new Row("if String.length(s) == 0 then "
                    + "Digit(0 - String.length(String.trim(s))) else Digit(0)", false),
            new Row("if String.length(s) == 1 then "
                    + "Digit(0 - String.length(String.trim(s))) else Digit(0)", true),
            // What a container holding something says of the arguments, read from a guard on how
            // many it holds — one way written twice is that one way.
            new Row("if String.length(s ++ s) >= 1 then Digit(String.length(s) - 1) else Digit(0)",
                    false),
            // A string inside another is no longer than it, and not standing inside says nothing.
            new Row("if String.startsWith(\"JP\", s) then Digit(String.length(s) - 2) "
                    + "else Digit(0)", false),
            new Row("if String.startsWith(\"JP\", s) then Digit(String.length(s) - 3) "
                    + "else Digit(0)", true),
            new Row("if String.contains(t, s) then "
                    + "Digit(String.length(s) - String.length(t)) else Digit(0)", false),
            new Row("if String.contains(t, s) then "
                    + "Digit(String.length(t) - String.length(s)) else Digit(0)", true),
            new Row("if String.endsWith(t, s) then Digit(0) "
                    + "else Digit(String.length(s) - String.length(t))", true),
            // How many some element of another set is not, as how many there are less those.
            new Row("Digit(Set.size(Set.union(a, b)) - Set.size(a))", false),
            new Row("Digit(Set.size(a) - Set.size(Set.union(a, b)))", true),
            // A closure that answers the element is no closure to count by: how many different
            // values the elements come to is one number whichever way it is asked for.
            new Row("Digit(List.length(List.distinct(xs)) - Map.size(List.groupBy(n -> n, xs)))",
                    false),
            new Row("Digit(Map.size(List.groupBy(n -> n, xs)) - Set.size(Set.fromList(xs)))",
                    false),
            new Row("Digit(List.length(List.distinctBy(n -> n, xs)) - List.length(List.distinct(xs)))",
                    false),
            new Row("Digit(List.length(List.distinctBy(n -> n + 1, xs)) "
                    + "- List.length(List.distinct(xs)))", true),
            // Above 2 and at least 3 are one statement of whole numbers.
            new Row("Digit(List.length(List.filter(n -> n > 2, xs)) "
                    + "- List.length(List.filter(n -> n >= 3, xs)))", false),
            new Row("Digit(List.length(List.filter(n -> n >= 3, xs)) "
                    + "- List.length(List.filter(n -> n > 2, xs)))", false),
            new Row("Digit(List.length(List.filter(n -> n <= 2, xs)) "
                    + "- List.length(List.filter(n -> n < 3, xs)))", false),
            new Row("Digit(List.length(xs) - List.length(List.filter(n -> n >= 3, xs)) "
                    + "- List.length(List.filter(n -> n < 3, xs)))", false),
            new Row("Digit(List.length(List.filter(n -> n > 2, xs)) "
                    + "- List.length(List.filter(n -> n >= 2, xs)))", true),
            // Two equalities between counts say what neither says alone.
            new Row("Digit(List.length(xs ++ ys) - List.length(ys ++ xs))", false),
            new Row("Digit(List.length(xs ++ ys) - List.length(List.concat([xs, ys])))", false),
            new Row("Digit(List.length(xs ++ ys) - List.length(ys ++ xs) - 1)", true),
            // What a statement over whole numbers holds of is the statement: the same set is one
            // count, a set inside another is no more, two that share nothing are no more together
            // than there are, and two that are every number between them are no fewer.
            new Row("Digit(List.length(List.filter(n -> n > 2 && n > 1, xs)) "
                    + "- List.length(List.filter(n -> n > 2, xs)))", false),
            new Row("Digit(List.length(List.filter(n -> n > 2, xs)) "
                    + "- List.length(List.filter(n -> n > 2 && n > 1, xs)))", false),
            new Row("Digit(List.length(List.filter(n -> n > 1, xs)) "
                    + "- List.length(List.filter(n -> n > 2, xs)))", false),
            new Row("Digit(List.length(List.filter(n -> n > 2, xs)) "
                    + "- List.length(List.filter(n -> n > 1, xs)))", true),
            new Row("Digit(List.length(List.filter(n -> n > 2 || n > 1, xs)) "
                    + "- List.length(List.filter(n -> n > 2, xs)))", false),
            new Row("if List.any(n -> n > 2, xs) && List.any(n -> n < 2, xs) then "
                    + "Digit(List.length(xs) - 2) else Digit(0)", false),
            new Row("if List.any(n -> n > 2, xs) && List.any(n -> n < 4, xs) then "
                    + "Digit(List.length(xs) - 2) else Digit(0)", true),
            new Row("Digit(List.length(List.filter(n -> n > 2, xs)) "
                    + "+ List.length(List.filter(n -> n < 5, xs)) - List.length(xs))", false),
            new Row("Digit(List.length(List.filter(n -> n > 2, xs)) "
                    + "+ List.length(List.filter(n -> n < 2, xs)) - List.length(xs))", true),
            new Row("Digit(List.length(List.filter(n -> n > 2 && n < 8, xs)) "
                    + "+ List.length(List.filter(n -> n <= 2 || n >= 8, xs)) - List.length(xs))",
                    false),
            new Row("Digit(List.length(xs) - List.length(List.filter(n -> n > 2 && n < 8, xs)) "
                    + "- List.length(List.filter(n -> n <= 2 || n >= 8, xs)))", false),
            new Row("Digit(List.length(xs) - List.length(List.filter(n -> n > 2, xs)) "
                    + "- List.length(List.filter(n -> n <= 1, xs)))", false),
            new Row("Digit(List.length(xs) - List.length(List.filter(n -> n > 2, xs)) "
                    + "- List.length(List.filter(n -> n <= 3, xs)))", true),
            // A fold written out is not the library's sum: the sum gets through where the fold
            // stops at a step, so what is known of one is not known of the other.
            new Row("Digit(List.sum(xs) - List.fold((acc, n) -> acc + n, 0, xs))", true),
            // A statement about how many an element holds is a statement over whole numbers like
            // any other: the elements that hold at least one are the elements that hold something,
            // and a sum of how many each holds is no less than the least each holds for as many
            // as hold at least that.
            new Row("Digit(List.length(List.filter(ys -> List.length(ys) >= 1, xss)) "
                    + "- List.length(List.filter(ys -> List.length(ys) > 0, xss)))", false),
            new Row("Digit(List.length(List.filter(ys -> List.length(ys) > 0, xss)) "
                    + "- List.length(List.filter(ys -> List.length(ys) >= 1, xss)))", false),
            new Row("Digit(List.length(List.filter(ys -> List.length(ys) >= 1, xss)) "
                    + "- List.length(List.filter(ys -> List.length(ys) >= 2, xss)))", false),
            new Row("Digit(List.length(List.filter(ys -> List.length(ys) >= 2, xss)) "
                    + "- List.length(List.filter(ys -> List.length(ys) >= 1, xss)))", true),
            new Row("if List.all(ys -> List.length(ys) >= 1, xss) && List.length(xss) >= 1 then "
                    + "Digit(List.length(List.concat(xss)) - 1) else Digit(0)", false),
            new Row("if List.all(ys -> List.length(ys) >= 1, xss) && List.length(xss) >= 1 then "
                    + "Digit(List.length(List.concat(xss)) - 2) else Digit(0)", true),
            new Row("if List.all(ys -> List.length(ys) >= 2, xss) && List.length(xss) >= 1 then "
                    + "Digit(List.length(List.concat(xss)) - 2) else Digit(0)", false),
            new Row("if List.any(ys -> List.length(ys) >= 2, xss) then "
                    + "Digit(List.length(List.concat(xss)) - 2) else Digit(0)", false),
            new Row("if List.any(ys -> List.length(ys) >= 2, xss) then "
                    + "Digit(List.length(List.concat(xss)) - 3) else Digit(0)", true),
            // What a statement holds of among the elements a filter kept is what both hold of
            // among the elements it was handed.
            new Row("Digit(List.length(List.filter(n -> n > 2, List.filter(n -> n > 1, xs))) "
                    + "- List.length(List.filter(n -> n > 2, xs)))", false),
            new Row("Digit(List.length(List.filter(n -> n > 2, xs)) "
                    + "- List.length(List.filter(n -> n > 2, List.filter(n -> n > 1, xs))))",
                    false),
            new Row("if List.any(n -> n > 2, List.filter(n -> n > 1, xs)) then "
                    + "Digit(List.length(List.filter(n -> n > 2, xs)) - 1) else Digit(0)", false),
            new Row("Digit(List.length(List.filter(n -> n > 2, xs)) "
                    + "- List.length(List.filter(n -> n > 2, List.filter(n -> n < 5, xs))))",
                    false),
            new Row("Digit(List.length(List.filter(n -> n > 2, List.filter(n -> n < 5, xs))) "
                    + "- List.length(List.filter(n -> n > 2, xs)))", true),
            // A closure that answers a container written out answers the same number of them
            // whatever it is handed.
            new Row("Digit(List.length(List.flatMap(n -> [n, n], xs)) - 2 * List.length(xs))",
                    false),
            new Row("Digit(2 * List.length(xs) - List.length(List.flatMap(n -> [n, n], xs)))",
                    false),
            new Row("Digit(List.length(List.flatMap(n -> [n, n], xs)) - 3 * List.length(xs))",
                    true),
            new Row("Digit(List.length(List.flatMap(n -> [n], xs)) - List.length(xs))", false),
            new Row("Digit(List.length(List.flatMap(n -> if n > 2 then [n] else [n, n], xs)) "
                    + "- List.length(xs))", true),
            // Nothing between the strings joined is the strings put end to end.
            new Row("Digit(String.length(String.concat([s, t])) "
                    + "- String.length(String.join(\"\", [s, t])))", false),
            new Row("Digit(String.length(String.join(\"\", [s, t])) "
                    + "- String.length(String.concat([s, t])))", false),
            new Row("Digit(String.length(String.concat([s, t])) "
                    + "- String.length(String.join(\",\", [s, t])))", true),
            // A join is the append it is, however it is written.
            new Row("Digit(List.length(xs ++ xs) - List.length(List.append(xs, xs)))", false),
            new Row("Digit(List.length(List.append(xs, xs)) - List.length(xs ++ xs))", false),
            new Row("Digit(List.length(xs ++ xs) - List.length(List.append(xs, xs)) - 1)", true),
            new Row("Digit(String.length(s ++ t) - String.length(String.append(s, t)))", false),
            new Row("Digit(String.length(s ++ t) - String.length(String.append(t, s)))", true),
            // A closure that answers the denial of another's is how many there are less how many
            // the other holds of.
            new Row("if List.all(n -> n > 2, xs) then Digit(0) "
                    + "else Digit(List.length(List.filter(n -> n <= 2, xs)) - 1)", false),
            new Row("if List.all(n -> n > 2, xs) then Digit(0) "
                    + "else Digit(List.length(List.filter(n -> n < 2, xs)) - 1)", true),
            new Row("if List.any(n -> n <= 2, xs) then "
                    + "Digit(List.length(xs) - List.length(List.filter(n -> n > 2, xs)) - 1) "
                    + "else Digit(0)", false),
            new Row("if List.any(n -> n <= 2, xs) then "
                    + "Digit(List.length(xs) - List.length(List.filter(n -> n > 2, xs)) - 2) "
                    + "else Digit(0)", true),
            new Row("Digit(List.length(List.filter(n -> n > 2, xs)) "
                    + "+ List.length(List.filter(n -> n <= 2, xs)) - List.length(xs))", false),
            new Row("Digit(List.length(xs) - List.length(List.filter(n -> n > 2, xs)) "
                    + "- List.length(List.filter(n -> n <= 2, xs)))", false),
            // A walk over none answers where it started, so an answer away from there is one over
            // something, whatever the step.
            new Row("if List.sum(xs) >= 3 then Digit(List.length(xs) - 1) else Digit(0)", false),
            new Row("if List.sum(xs) >= 0 then Digit(List.length(xs) - 1) else Digit(0)", true),
            new Row("if List.sum(xs) > 0 then Digit(List.length(xs) - 2) else Digit(0)", true),
            new Row("if List.sum(xs) > 0 then Digit(0) else Digit(List.length(xs) - 1)", true),
            new Row("if List.fold((acc, n) -> acc + n, 5, xs) > 5 then "
                    + "Digit(List.length(xs) - 1) else Digit(0)", false),
            new Row("if List.fold((acc, n) -> acc + n, 5, xs) > 4 then "
                    + "Digit(List.length(xs) - 1) else Digit(0)", true),
            new Row("if List.sum(List.map(n -> n + 1, xs)) > 0 then "
                    + "Digit(List.length(xs) - 1) else Digit(0)", false),
            // An intersection holds no more than either set, and something only where both do.
            new Row("Digit(Set.size(b) - Set.size(Set.intersection(a, b)))", false),
            new Row("Digit(Set.size(Set.intersection(a, b)) - Set.size(b))", true),
            new Row("if Set.size(Set.intersection(a, b)) >= 1 then Digit(Set.size(b) - 1) "
                    + "else Digit(0)", false),
            new Row("if Set.size(Set.intersection(a, b)) >= 1 then Digit(Set.size(b) - 2) "
                    + "else Digit(0)", true),
            new Row("if Set.size(Set.difference(a, b)) >= 1 then Digit(Set.size(b) - 1) "
                    + "else Digit(0)", true),
            // Of two sets, how many of one the other holds is how many of the other the one holds,
            // so what is in both is counted once whichever way round it is asked, and the union
            // and the intersection together hold what the two do.
            new Row("Digit(Set.size(Set.union(a, b)) + Set.size(Set.intersection(a, b)) "
                    + "- Set.size(a) - Set.size(b))", false),
            new Row("Digit(Set.size(a) + Set.size(b) - Set.size(Set.union(a, b)) "
                    + "- Set.size(Set.intersection(a, b)))", false),
            new Row("Digit(Set.size(Set.intersection(a, b)) - Set.size(Set.intersection(b, a)))",
                    false),
            new Row("Digit(Set.size(Set.union(a, b)) + Set.size(Set.difference(a, b)) "
                    + "- Set.size(a) - Set.size(b))", true),
            new Row("Digit(Set.size(Set.union(a, b)) + Set.size(Set.intersection(a, b)) "
                    + "- Set.size(a) - Set.size(b) - 1)", true),
            // The same of the keys of two maps.
            new Row("Digit(Map.size(mb) - Map.size(Map.intersection(ma, mb)))", false),
            new Row("Digit(Map.size(ma) - Map.size(Map.intersection(ma, mb)))", false),
            new Row("Digit(Map.size(Map.intersection(ma, mb)) - Map.size(mb))", true));

    @Test
    void eachRowIsOwedWhatItsLawLeavesOpen() {
        List<String> wrong = new ArrayList<>();
        for (Row row : ROWS) {
            Compilation compilation = Compilation.ofSource("""
                    module demo

                    data Digit = Int
                        invariant atLeastNought = value >= 0

                    behavior f : (xs: List<Int>, ys: List<Int>, xss: List<List<Int>>,
                                  a: Set<Int>, b: Set<Int>, ma: Map<String, Int>, mb: Map<String, Int>,
                                  s: String, t: String, x: Int)
                        -> Digit
                        constructs Digit
                    let f (xs, ys, xss, a, b, ma, mb, s, t, x) =
                        %s
                    """.formatted(row.body()), "Main");
            compilation.answerEverything();
            List<Located> refused = compilation.errors().stream()
                    .filter(each -> !"E2010".equals(each.diagnostic().code())).toList();
            assertTrue(refused.isEmpty(), () -> row.body() + " compiles: " + refused);
            boolean owed = compilation.errors().size() > refused.size()
                    || compilation.warnings().stream().anyMatch(each ->
                    each.diagnostic().severity() == Severity.WARNING
                            && "E2011".equals(each.diagnostic().code()));
            if (owed != row.owed()) {
                wrong.add(row.body() + ": owed " + owed + ", expected " + row.owed());
            }
        }
        assertEquals(List.of(), wrong, "each row is owed exactly what its law leaves open");
    }

    /**
     * No law of the library states two values being one but of an element and what the element is
     * asked to be, which is how many elements are that value. The discharge names it nowhere else;
     * a law that states it of two arguments is read as saying nothing there, and is then a row
     * above to write.
     */
    @Test
    void twoValuesBeingOneIsStatedOnlyOfAnElement() {
        List<String> stated = new ArrayList<>();
        DefaultBoundOperationFacts.get().settled().forEach((operation, settled) ->
                settled.forEach((observed, settling) -> {
                    if (settling instanceof BoundOperationFacts.Settled.ByALaw(var law, var _)
                            && statesOneValueOutsideAnElement(law)) {
                        stated.add(operation + " " + observed);
                    }
                }));
        assertEquals(List.of(), stated);
    }

    private static boolean statesOneValueOutsideAnElement(OperationLaw<?> law) {
        return switch (law) {
            case OperationLaw.Observation<?>(var _, var equivalent) -> outside(equivalent);
            case OperationLaw.Size<?> size -> size.cases().stream()
                    .anyMatch(each -> outside(each.where()));
        };
    }

    /** Whether {@code part} states two values being one other than inside what is asked of an
     *  element: every number of a law that asks something of a value asks it of an element. */
    private static boolean outside(LawProposition<?> part) {
        return switch (part) {
            case LawProposition.Same<?> _ -> true;
            case LawProposition.All<?> all -> all.parts().stream()
                    .anyMatch(AGuardOverALibraryOperationSettlesWhatItsLawSaysTest::outside);
            case LawProposition.Any<?> any -> any.parts().stream()
                    .anyMatch(AGuardOverALibraryOperationSettlesWhatItsLawSaysTest::outside);
            case LawProposition.SomeElement<?> _, LawProposition.Always<?> _,
                 LawProposition.Observed<?> _, LawProposition.Inside<?> _,
                 LawProposition.Compared<?> _ -> false;
        };
    }
}
