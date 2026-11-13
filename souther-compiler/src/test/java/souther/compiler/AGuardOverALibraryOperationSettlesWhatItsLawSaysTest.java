package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.diag.Severity;
import souther.compiler.query.Compilation;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.OperationLaw;

import java.math.BigInteger;
import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.function.IntFunction;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

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
            // The empty string stands inside every string, so one that does not is not empty —
            // and that is all the denial says of it.
            new Row("if String.contains(t, s) then Digit(0) "
                    + "else Digit(String.length(t) - 1)", false),
            new Row("if String.startsWith(t, s) then Digit(0) "
                    + "else Digit(String.length(t) - 1)", false),
            new Row("if String.endsWith(t, s) then Digit(0) "
                    + "else Digit(String.length(t) - 1)", false),
            new Row("if String.contains(t, s) then Digit(0) "
                    + "else Digit(String.length(t) - 2)", true),
            new Row("if String.contains(t, s) then Digit(0) "
                    + "else Digit(String.length(s) - String.length(t))", true),
            new Row("if String.contains(t, s) then Digit(String.length(t) - 1) "
                    + "else Digit(0)", true),
            // The empty string stands inside every string, so what is not inside is never it.
            new Row("if String.contains(\"\", s) then Digit(0) "
                    + "else Digit(String.length(s) - 1)", false),
            new Row("if String.contains(\"a\", s) then Digit(0) "
                    + "else Digit(String.length(s) - 1)", true),
            // A string a pattern accepts holds as many code points as its strings do, and one it
            // does not accept is not empty where the pattern accepts that.
            new Row("if String.matches(\"[0-9]{3}\", t) then Digit(String.length(t) - 3) "
                    + "else Digit(0)", false),
            new Row("if String.matches(\"[0-9]{3}\", t) then Digit(String.length(t) - 4) "
                    + "else Digit(0)", true),
            new Row("if String.matches(\"[0-9]{3}\", t) then Digit(3 - String.length(t)) "
                    + "else Digit(0)", false),
            new Row("if String.matches(\"[0-9]{3}\", t) then Digit(2 - String.length(t)) "
                    + "else Digit(0)", true),
            new Row("if String.matches(\"[0-9]{3}\", t) then Digit(0) "
                    + "else Digit(String.length(t) - 1)", true),
            new Row("if String.matches(\"[0-9]*\", t) then Digit(0) "
                    + "else Digit(String.length(t) - 1)", false),
            new Row("if String.matches(\"[0-9]*\", t) then Digit(String.length(t) - 1) "
                    + "else Digit(0)", true),
            new Row("if String.matches(\"[0-9]+\", t) then Digit(String.length(t) - 1) "
                    + "else Digit(0)", false),
            new Row("if String.matches(\"[0-9]+\", t) then Digit(String.length(t) - 2) "
                    + "else Digit(0)", true),
            new Row("if String.matches(\"[A-Z]{2,4}\", t) then Digit(String.length(t) - 2) "
                    + "else Digit(0)", false),
            new Row("if String.matches(\"[A-Z]{2,4}\", t) then Digit(4 - String.length(t)) "
                    + "else Digit(0)", false),
            new Row("if String.matches(\"[A-Z]{2,4}\", t) then Digit(3 - String.length(t)) "
                    + "else Digit(0)", true),
            new Row("if String.matches(\"[0-9]{3}|[A-Z]{5}\", t) "
                    + "then Digit(String.length(t) - 3) else Digit(0)", false),
            new Row("if String.matches(\"[0-9]{3}|[A-Z]{5}\", t) "
                    + "then Digit(String.length(t) - 4) else Digit(0)", true),
            // A conjunction that does not hold leaves either part possible, so neither part's
            // denial is taken.
            new Row("if String.contains(t, s) && String.contains(u, s) then Digit(0) "
                    + "else Digit(String.length(t) - 1)", true),
            new Row("if String.contains(t, s) || String.contains(u, s) then Digit(0) "
                    + "else Digit(String.length(t) - 1)", false),
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
            // A filter of a filter keeps the elements both keep, whichever container it is of.
            new Row("Digit(List.length(List.filter(n -> n > 2, List.filter(n -> n > 1, xs))) "
                    + "- List.length(List.filter(n -> n > 2, xs)))", false),
            new Row("Digit(Set.size(Set.filter(n -> n > 2, Set.filter(n -> n > 1, a))) "
                    + "- Set.size(Set.filter(n -> n > 2, a)))", false),
            new Row("Digit(Set.size(Set.filter(n -> n > 2, a)) "
                    + "- Set.size(Set.filter(n -> n > 2, Set.filter(n -> n > 1, a))) - 1)", true),
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
            // A total over the same elements in another order is the same number, and a total over
            // an append is the two totals added, or multiplied. The library's sum and product hold
            // only their answer to an Int and not each step, so the relation is among the numbers
            // they answer and says nothing of a fold.
            new Row("Digit(List.sum(List.reverse(xs)) - List.sum(xs))", false),
            new Row("Digit(List.sum(xs) - List.sum(List.sort(xs)))", false),
            new Row("Digit(List.sum(ys ++ xs) - List.sum(xs ++ ys))", false),
            new Row("Digit(List.sum(xs ++ ys) - List.sum(xs) - List.sum(ys))", false),
            new Row("Digit(List.sum(xs) + List.sum(ys) - List.sum(xs ++ ys))", false),
            new Row("Digit(List.sum(xs ++ ys) - List.sum(xs) - List.sum(ys) - 1)", true),
            new Row("Digit(List.sum(xs ++ ys) - List.sum(xs))", true),
            new Row("Digit(List.sum(xs ++ xs) - List.sum(xs) - List.sum(xs))", false),
            new Row("Digit(List.sum(xs ++ ys) - List.sum(List.reverse(xs) ++ ys))", false),
            new Row("Digit(List.sum(xs) - List.sum(ys))", true),
            // An append of three is the three added, and the same container twice is added twice.
            new Row("Digit(List.sum(xs ++ ys ++ xs) - List.sum(xs) - List.sum(xs) - List.sum(ys))",
                    false),
            new Row("Digit(List.sum(xs ++ ys ++ xs) - List.sum(xs) - List.sum(ys))", true),
            new Row("Digit(List.sum(List.concat([xs, ys, xs])) "
                    + "- List.sum(xs) - List.sum(xs) - List.sum(ys))", false),
            new Row("Digit(List.sum(xs ++ ys ++ xs) - List.sum(xs ++ ys) - List.sum(xs))", false),
            new Row("Digit(List.product(List.reverse(xs)) - List.product(xs))", false),
            new Row("Digit(List.product(ys ++ xs) - List.product(xs ++ ys))", false),
            new Row("Digit(List.product(xs ++ ys) - List.product(xs) * List.product(ys))", false),
            new Row("Digit(List.product(xs ++ ys) - List.product(ys) * List.product(xs))", false),
            new Row("Digit(List.product(xs ++ ys) - List.product(xs) * List.product(ys) - 1)",
                    true),
            new Row("Digit(List.product(xs ++ ys) - List.product(xs) - List.product(ys))", true),
            new Row("Digit(List.sum(List.concat([xs, ys])) - List.sum(xs) - List.sum(ys))", false),
            new Row("Digit(List.sum(List.concat([xs, ys])) - List.sum(xs) - List.sum(ys) - 1)",
                    true),
            new Row("Digit(List.sum(List.reverse(xs)) - List.product(xs))", true),
            new Row("Digit(List.sum(xs ++ []) - List.sum(xs))", false),
            // What an exact total is is no number of the type of the call: the sum of xs here is
            // twice the greatest Int, which no call of it answers, and the run [MAX, MAX] ++
            // [-MAX] is still one the guard lets through to a violation.
            new Row("if List.sum(xs ++ ys) == 9223372036854775807 "
                    + "&& List.sum(ys) == 0 - 9223372036854775807 then Digit(0 - 1) else Digit(0)",
                    true),
            new Row("if List.sum(xs ++ ys) == 9223372036854775807 && List.sum(ys) == -1 "
                    + "then Digit(0 - 1) else Digit(0)", true),
            new Row("if List.sum(List.map(n -> n * 2, xs)) == 9223372036854775806 "
                    + "&& List.sum(xs) == 4611686018427387903 then Digit(0 - 1) else Digit(0)",
                    true),
            new Row("if List.product(xs ++ ys) == 0 && List.product(ys) == 0 "
                    + "then Digit(0 - 1) else Digit(0)", true),
            // The same through a name the list was given.
            new Row("{ let zs = xs ++ ys\n Digit(List.sum(zs) - List.sum(xs) - List.sum(ys)) }",
                    false),
            new Row("{ let zs = xs ++ ys\n Digit(List.sum(List.reverse(zs)) - List.sum(ys ++ xs)) }",
                    false),
            new Row("{ let zs = List.filter(n -> n > 2, xs)\n "
                    + "Digit(List.sum(List.map(n -> n * 2, zs)) - 2 * List.sum(zs)) }", false),
            new Row("{ let zs = xs ++ ys\n Digit(List.sum(zs) - List.sum(xs) - List.sum(ys) - 1) }",
                    true),
            new Row("Digit(List.product(xs ++ ys ++ xs) "
                    + "- List.product(xs) * List.product(xs) * List.product(ys))", false),
            new Row("Digit(List.product(xs ++ ys ++ xs) - List.product(xs ++ ys) * List.product(xs))",
                    false),
            // What an element-wise call makes of each side of an append, or of a list in another
            // order, is totalled the same way, and a total of a mapping by a line of the element is
            // that line of the total.
            new Row("Digit(List.sum(List.map(n -> n + 1, xs ++ ys)) "
                    + "- List.sum(List.map(n -> n + 1, xs)) - List.sum(List.map(n -> n + 1, ys)))",
                    false),
            new Row("Digit(List.sum(List.map(n -> n + 1, List.reverse(xs))) "
                    + "- List.sum(List.map(n -> n + 1, xs)))", false),
            new Row("Digit(List.sum(List.map(n -> n + 1, xs ++ ys)) "
                    + "- List.sum(List.map(n -> n + 2, xs)) - List.sum(List.map(n -> n + 1, ys)))",
                    true),
            new Row("Digit(List.sum(List.map(n -> n + 1, xs)) - List.sum(xs) - List.length(xs))",
                    false),
            new Row("Digit(List.sum(List.map(n -> n + 1, xs)) - List.sum(xs) - List.length(xs) - 1)",
                    true),
            new Row("Digit(List.sum(List.map(n -> n * 2, xs)) - 2 * List.sum(xs))", false),
            new Row("Digit(List.sum(List.map(n -> n * 2, xs)) - 3 * List.sum(xs))", true),
            new Row("Digit(List.sum(List.map(n -> 3 - n, xs)) - 3 * List.length(xs) + List.sum(xs))",
                    false),
            new Row("Digit(List.sum(List.map(n -> n * 2, xs ++ ys)) "
                    + "- 2 * List.sum(xs) - 2 * List.sum(ys))", false),
            // A list split into what holds each of its elements once is the total of what it is
            // split into: a filter and the filter of its denial, a take and the drop of the same
            // count, under what is done to each element.
            new Row("Digit(List.sum(List.filter(n -> n > 2, xs)) "
                    + "+ List.sum(List.filter(n -> n <= 2, xs)) - List.sum(xs))", false),
            new Row("Digit(List.sum(List.filter(n -> n > 2, xs)) "
                    + "+ List.sum(List.filter(n -> n <= 2, xs)) - List.sum(xs) - 1)", true),
            new Row("Digit(List.sum(List.filter(n -> n > 2, xs)) "
                    + "+ List.sum(List.filter(n -> n <= 3, xs)) - List.sum(xs))", true),
            new Row("Digit(List.sum(List.take(3, xs)) + List.sum(List.drop(3, xs)) - List.sum(xs))",
                    false),
            new Row("Digit(List.sum(List.take(3, xs)) + List.sum(List.drop(4, xs)) - List.sum(xs))",
                    true),
            new Row("Digit(List.sum(List.map(n -> n * 2, List.filter(n -> n > 2, xs))) "
                    + "+ List.sum(List.map(n -> n * 2, List.filter(n -> n <= 2, xs))) "
                    + "- 2 * List.sum(xs))", false),
            new Row("Digit(List.product(List.take(2, xs)) * List.product(List.drop(2, xs)) "
                    + "- List.product(xs))", false),
            new Row("Digit(List.product(List.filter(n -> n > 2, xs)) "
                    + "* List.product(List.filter(n -> n <= 2, xs)) - List.product(xs))", false),
            new Row("Digit(List.product(List.filter(n -> n > 2, xs)) "
                    + "* List.product(List.filter(n -> n <= 3, xs)) - List.product(xs))", true),
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
            // A filter of a map's entries keeps the entries both statements of a key and a value
            // hold of.
            new Row("Digit(Map.size(Map.filterEntries((k, v) -> v > 2, "
                    + "Map.filterEntries((k, v) -> k == \"a\", ma))) "
                    + "- Map.size(Map.filterEntries((k, v) -> k == \"a\" && v > 2, ma)))", false),
            new Row("Digit(Map.size(Map.filterEntries((k, v) -> k == \"a\" && v > 2, ma)) "
                    + "- Map.size(Map.filterEntries((k, v) -> v > 2, "
                    + "Map.filterEntries((k, v) -> k == \"a\", ma))))", false),
            new Row("Digit(Map.size(Map.filterEntries((k, v) -> v > 2, "
                    + "Map.filterEntries((k, v) -> k == \"a\", ma))) "
                    + "- Map.size(Map.filterEntries((k, v) -> k == \"a\" && v > 2, ma)) - 1)",
                    true),
            new Row("Digit(Map.size(Map.filterEntries((k, v) -> v > 2, "
                    + "Map.filterEntries((k, v) -> k == \"a\", ma))) "
                    + "- Map.size(Map.filterEntries((k, v) -> k == \"b\" && v > 2, ma)))", true),
            // The same of the keys of two maps.
            new Row("Digit(Map.size(mb) - Map.size(Map.intersection(ma, mb)))", false),
            new Row("Digit(Map.size(ma) - Map.size(Map.intersection(ma, mb)))", false),
            new Row("Digit(Map.size(Map.intersection(ma, mb)) - Map.size(mb))", true));

    @Test
    void eachRowIsOwedWhatItsLawLeavesOpen() {
        List<String> wrong = new ArrayList<>();
        for (Row row : ROWS) {
            boolean owed = owedBy(row.body());
            if (owed != row.owed()) {
                wrong.add(row.body() + ": owed " + owed + ", expected " + row.owed());
            }
        }
        assertEquals(List.of(), wrong, "each row is owed exactly what its law leaves open");
    }

    /**
     * A condition stated through a helper makes certain what the same condition written out does:
     * which pattern a call is written with, and which side of it the path is on, do not turn on
     * whether a name stands between the guard and the call.
     */
    @Test
    void aGuardStatedThroughAHelperSaysWhatTheSameGuardWrittenOutSays() {
        List<String> wrong = new ArrayList<>();
        for (String guard : List.of("String.matches(\"B{5}\", s)", "five(s)")) {
            for (Row row : List.of(
                    new Row("if %s then Digit(String.length(s) - 5) else Digit(0)", false),
                    new Row("if %s then Digit(String.length(s) - 6) else Digit(0)", true),
                    new Row("if %s then Digit(0) else Digit(String.length(s) - 5)", true))) {
                String body = row.body().formatted(guard);
                boolean owed = owedBy("""
                        module demo

                        data Digit = Int
                            invariant atLeastNought = value >= 0

                        let five (x: String): Bool = String.matches("B{5}", x)

                        behavior f : (s: String) -> Digit
                            constructs Digit
                        let f (s) =
                            %s
                        """.formatted(body), body);
                if (owed != row.owed()) {
                    wrong.add(body + ": owed " + owed + ", expected " + row.owed());
                }
            }
        }
        assertEquals(List.of(), wrong, "a name between the guard and the call changes nothing");
    }

    /** The totals of lists of decimals are related as those of lists of integers are, and the
     *  row beside each moves one side by one. */
    private static final List<Row> ROWS_OF_DECIMALS = List.of(
            new Row("Share(List.sum(xs ++ ys) - List.sum(xs) - List.sum(ys))", false),
            new Row("Share(List.sum(xs ++ ys) - List.sum(xs) - List.sum(ys) - 1m)", true),
            new Row("Share(List.sum(List.reverse(xs)) - List.sum(xs))", false),
            new Row("Share(List.sum(List.reverse(xs)) - List.sum(ys))", true),
            new Row("Share(List.sum(List.map(n -> n * 2m, xs ++ ys)) - 2m * List.sum(xs) "
                    + "- 2m * List.sum(ys))", false),
            new Row("Share(List.sum(List.map(n -> n * 2m, xs ++ ys)) - 2m * List.sum(xs) "
                    + "- 3m * List.sum(ys))", true),
            new Row("Share(List.sum(List.filter(n -> n > 2m, xs)) "
                    + "+ List.sum(List.filter(n -> n <= 2m, xs)) - List.sum(xs))", false),
            new Row("Share(List.sum(List.filter(n -> n > 2m, xs)) "
                    + "+ List.sum(List.filter(n -> n < 2m, xs)) - List.sum(xs))", true),
            new Row("Share(List.product(xs ++ ys) - List.product(xs) * List.product(ys))", false),
            new Row("Share(List.product(xs ++ ys) - List.product(xs) * List.product(xs))", true));

    /** What a call answers only where it answers: {@code xs = [MAX, 1]} and {@code ys = [-1]} add
     *  up to {@code MAX} as a whole and the call over {@code xs} alone answers nothing, so no row
     *  that reads the call in a branch it is not evaluated in may rule out the branch that is. */
    private static final List<Row> ROWS_OF_CALLS_NOT_EVALUATED = List.of(
            new Row("if List.sum(xs ++ ys) == 9223372036854775807 && List.sum(ys) == -1 then "
                    + "Digit(0 - 1) else if List.sum(xs) == 0 then Digit(0) else Digit(0)", true),
            new Row("if List.sum(xs ++ ys) == 9223372036854775807 && List.sum(ys) == -1 then "
                    + "Digit(0 - 1) else Digit(0)", true),
            new Row("if List.sum(xs ++ ys) == 9223372036854775807 && List.sum(ys) == -1 then "
                    + "Digit(0) else if List.sum(xs) == 0 then Digit(0 - 1) else Digit(0)", true),
            new Row("if List.sum(xs ++ ys) == 9223372036854775807 && List.sum(ys) == -1 then "
                    + "Digit(0) else if List.sum(xs) == 0 then Digit(0) else Digit(0)", false));

    @Test
    void aCallNotEvaluatedOnAPathRulesNothingOutOfIt() {
        List<String> wrong = new ArrayList<>();
        for (Row row : ROWS_OF_CALLS_NOT_EVALUATED) {
            boolean owed = owedBy(row.body());
            if (owed != row.owed()) {
                wrong.add(row.body() + ": owed " + owed + ", expected " + row.owed());
            }
        }
        assertEquals(List.of(), wrong, "each row is owed exactly what its law leaves open");
    }

    @Test
    void eachRowOfDecimalsIsOwedWhatItsLawLeavesOpen() {
        List<String> wrong = new ArrayList<>();
        for (Row row : ROWS_OF_DECIMALS) {
            boolean owed = owedByDecimals(row.body());
            if (owed != row.owed()) {
                wrong.add(row.body() + ": owed " + owed + ", expected " + row.owed());
            }
        }
        assertEquals(List.of(), wrong, "each row is owed exactly what its law leaves open");
    }

    /** Whether the discharge leaves anything owed of a behavior with {@code body}. */
    private static boolean owedBy(String body) {
        return owedBy("""
                module demo

                data Digit = Int
                    invariant atLeastNought = value >= 0

                behavior f : (xs: List<Int>, ys: List<Int>, xss: List<List<Int>>,
                              a: Set<Int>, b: Set<Int>, ma: Map<String, Int>, mb: Map<String, Int>,
                              s: String, t: String, u: String, x: Int)
                    -> Digit
                    constructs Digit
                let f (xs, ys, xss, a, b, ma, mb, s, t, u, x) =
                    %s
                """.formatted(body), body);
    }

    /** The same over lists of decimals, which have no end to run over. */
    private static boolean owedByDecimals(String body) {
        return owedBy("""
                module demo

                data Share = Decimal
                    invariant atLeastNought = value >= 0m

                behavior f : (xs: List<Decimal>, ys: List<Decimal>) -> Share
                    constructs Share
                let f (xs, ys) =
                    %s
                """.formatted(body), body);
    }

    private static boolean owedBy(String source, String body) {
        Compilation compilation = ACompiledModel.refusedOnlyWith(Set.of("E2010"),
                Compilation.ofSource(source, "Main"));
        return !compilation.errors().isEmpty()
                || compilation.warnings().stream().anyMatch(each ->
                each.diagnostic().severity() == Severity.WARNING
                        && "E2011".equals(each.diagnostic().code()));
    }

    /** {@code xs} put together with itself {@code times} times over, one name for each step, and
     *  the sum of what that comes to less {@code 2^times} of the sum of {@code xs} — or, where
     *  that is more than an {@code Int} is written as, less the sum of the step before twice. */
    private static String doubled(int times) {
        StringBuilder body = new StringBuilder("{ let a0 = xs\n");
        for (int step = 1; step <= times; step++) {
            body.append("  let a").append(step).append(" = a").append(step - 1).append(" ++ a")
                    .append(step - 1).append('\n');
        }
        body.append("  Digit(List.sum(a").append(times).append(") - ");
        BigInteger copies = BigInteger.TWO.pow(times);
        return (copies.bitLength() < Long.SIZE
                ? body.append(copies).append(" * List.sum(xs)) }")
                : body.append("List.sum(a").append(times - 1).append(") - List.sum(a")
                        .append(times - 1).append(")) }")).toString();
    }

    /** A list put together one more list at a time, each a list of its own, as many steps as
     *  {@code length} and one name for each, then {@code last} of the names. */
    private static String chained(int length, IntFunction<String> last) {
        StringBuilder body = new StringBuilder("{ let a0 = [x]\n");
        for (int step = 1; step < length; step++) {
            body.append("  let a").append(step).append(" = a").append(step - 1).append(" ++ [x + ")
                    .append(step).append("]\n");
        }
        return body.append("  ").append(last.apply(length - 1)).append(" }").toString();
    }

    /**
     * Every step of a chain holds the leaves of the step before it and one more, so what is held
     * for the steps comes to the square of the length. The source bounds the length (E2107), and
     * at the longest it allows the relation is still read, in the time the rest of the check
     * takes.
     */
    @Test
    void aListPutTogetherOfAsManyListsAsASourceMayWriteIsTakenApart() {
        assertTimeoutPreemptively(Duration.ofSeconds(60), () -> {
            assertEquals(false, owedBy(chained(300,
                    last -> "Digit(List.sum(List.reverse(a" + last + ")) - List.sum(a" + last
                            + "))")), "the same elements, the other way round");
            assertEquals(true, owedBy(chained(300,
                    last -> "Digit(List.sum(List.reverse(a" + last + ")) - List.sum(a" + (last - 1)
                            + "))")), "one element fewer");
        });
    }

    /** The product of {@code xs} put together with itself {@code times} times over, less the
     *  product written of as many products of {@code xs}, each step the product before it
     *  multiplied by itself. */
    private static String doubledProduct(int times) {
        StringBuilder body = new StringBuilder("{ let a0 = xs\n  let m0 = List.product(xs)\n");
        for (int step = 1; step <= times; step++) {
            body.append("  let a").append(step).append(" = a").append(step - 1).append(" ++ a")
                    .append(step - 1).append("\n  let m").append(step).append(" = m")
                    .append(step - 1).append(" * m").append(step - 1).append('\n');
        }
        return body.append("  Digit(List.product(a").append(times).append(") - m").append(times)
                .append(") }").toString();
    }

    /**
     * A list put together of itself over and over is a shared term, and so is a product of a
     * product of itself: taking either apart is as many steps as it has terms and not as many as
     * it holds elements. Seventy steps hold more elements than any count says, and what holds
     * more is not read as a count.
     */
    @Test
    void aListPutTogetherOfItselfIsTakenApartOncePerTerm() {
        assertTimeoutPreemptively(Duration.ofSeconds(60), () -> {
            assertEquals(false, owedBy(doubled(3)), "eight times, which a count says");
            assertEquals(false, owedBy(doubled(40)), "a count a long holds");
            assertEquals(true, owedBy(doubled(70)), "more than a count says, so nothing is said");
            assertEquals(false, owedBy(doubledProduct(3)), "eight times, which a count says");
            assertEquals(false, owedBy(doubledProduct(40)), "a count a long holds");
            assertEquals(true, owedBy(doubledProduct(70)),
                    "more than a count says, so nothing is said");
        });
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
