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
            new Row("Digit(Set.size(a) - Set.size(Set.union(a, b)))", true));

    @Test
    void eachRowIsOwedWhatItsLawLeavesOpen() {
        List<String> wrong = new ArrayList<>();
        for (Row row : ROWS) {
            Compilation compilation = Compilation.ofSource("""
                    module demo

                    data Digit = Int
                        invariant atLeastNought = value >= 0

                    behavior f : (xs: List<Int>, xss: List<List<Int>>, a: Set<Int>, b: Set<Int>,
                                  s: String, t: String, x: Int) -> Digit
                        constructs Digit
                    let f (xs, xss, a, b, s, t, x) =
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
