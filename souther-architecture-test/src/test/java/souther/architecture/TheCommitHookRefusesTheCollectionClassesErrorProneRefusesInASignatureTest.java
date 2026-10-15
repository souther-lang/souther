package souther.architecture;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the pre-commit hook says about {@code ArrayList}, {@code LinkedList}, {@code HashSet},
 * {@code LinkedHashSet}, {@code TreeSet}, {@code HashMap}, {@code LinkedHashMap} and
 * {@code TreeMap}, held against what Error Prone's NonApiType says of the same source.
 *
 * <p>The hook is the same question asked of a parser, and what it must never do is refuse what CI
 * accepts, because that stops a commit nothing is wrong with. So each case is a source, and the
 * count of what Error Prone refuses in it is the count Error Prone gives when it is run over it
 * ({@link TheCommitHook}), not a count read off its documentation or its source. Both counts are
 * written down per case, and both are asserted, so a Checkstyle or an Error Prone that comes to
 * answer differently fails here and not in somebody's commit.
 *
 * <p>The hook may refuse less than Error Prone, and where it does the case says so with a count of
 * its own: a type variable's bound is something Error Prone reads and a parser cannot. It may not
 * refuse more, and every case is checked for that as well as for its own counts.
 */
class TheCommitHookRefusesTheCollectionClassesErrorProneRefusesInASignatureTest {

    /**
     * A source and how many times each of the two refuses something in it. {@code source} is a
     * compilation unit's types; {@code Fixture} in it names the class the test files it under.
     */
    private record Case(String name, String source, int errorProne, int hook) {
    }

    private static Case refusedByBoth(String name, String members) {
        return new Case(name, inClass(members), 1, 1);
    }

    private static Case acceptedByBoth(String name, String members) {
        return new Case(name, inClass(members), 0, 0);
    }

    private static String inClass(String members) {
        return "final class Fixture {\n    " + members + "\n}";
    }

    private static final List<Case> CASES = List.of(
            // Where a name is written.
            refusedByBoth("a result named for its class",
                    "ArrayList<String> f() { return null; }"),
            refusedByBoth("a parameter named for its class",
                    "void f(LinkedHashMap<String, String> m) { }"),
            refusedByBoth("a result that holds one in a type argument",
                    "Map<String, ArrayList<String>> f() { return null; }"),
            refusedByBoth("a parameter that holds one two type arguments down",
                    "void f(Map<String, List<TreeSet<String>>> m) { }"),
            refusedByBoth("a parameter that is not on the first line of the signature",
                    "void f(int n,\n               HashMap<String, String> m) { }"),
            refusedByBoth("a qualified name",
                    "java.util.HashSet<String> f() { return null; }"),
            refusedByBoth("a raw type",
                    "ArrayList f() { return null; }"),
            refusedByBoth("the upper bound of a wildcard",
                    "List<? extends ArrayList<String>> f() { return null; }"),
            refusedByBoth("a constructor parameter",
                    "Fixture(TreeMap<String, String> m) { }"),
            refusedByBoth("a method of an interface",
                    "interface Reads { LinkedList<String> all(); }"),
            refusedByBoth("a static method of an interface",
                    "interface Reads { static ArrayList<String> s() { return null; } }"),
            refusedByBoth("a static method",
                    "static ArrayList<String> f() { return null; }"),
            refusedByBoth("an abstract method",
                    "abstract static class Base { abstract ArrayList<String> f(); }"),
            refusedByBoth("a final parameter",
                    "void f(final ArrayList<String> m) { }"),
            refusedByBoth("an annotated parameter",
                    "void f(@Deprecated ArrayList<String> m) { }"),
            refusedByBoth("a method of an enum",
                    "enum E { A; ArrayList<String> f() { return null; } }"),
            new Case("a method of the body of an enum constant and the one it implements",
                    inClass("enum E { A { ArrayList<String> g() { return null; } }; abstract ArrayList<String> g(); }"),
                    2, 2),
            refusedByBoth("a method of an anonymous class",
                    "Object f() { return new Object() { ArrayList<String> g() { return null; } }; }"),
            new Case("two in one signature",
                    inClass("HashSet<String> f(HashMap<String, String> m) { return null; }"), 2, 2),
            new Case("an override and what it overrides",
                    "interface Reads { LinkedList<String> all(); }\n"
                            + "final class Fixture implements Reads {\n"
                            + "    @Override public LinkedList<String> all() { return null; }\n"
                            + "}", 2, 2),

            // What is not a parameter or a result.
            acceptedByBoth("a field",
                    "private final ArrayList<String> held = new ArrayList<>();"),
            acceptedByBoth("a local variable and what is built into it",
                    "List<String> f() { ArrayList<String> local = new ArrayList<>(); return local; }"),
            acceptedByBoth("a construction returned as the interface",
                    "List<String> f() { return new ArrayList<>(); }"),
            acceptedByBoth("the interfaces they implement",
                    "Map<String, List<String>> f(Map<String, String> m, List<String> l) { return null; }"),
            acceptedByBoth("the parameter of a lambda",
                    "Function<ArrayList<String>, Integer> f = (ArrayList<String> l) -> 1;"),
            acceptedByBoth("a class that extends one",
                    "static class Mine extends ArrayList<String> { }\n    Mine f() { return null; }"),

            // What Error Prone does not look into.
            acceptedByBoth("an array result",
                    "ArrayList<String>[] f() { return null; }"),
            acceptedByBoth("an array of arrays",
                    "ArrayList<String>[][] f() { return null; }"),
            acceptedByBoth("an array parameter",
                    "void f(ArrayList<String>[] xs) { }"),
            acceptedByBoth("a variable-arity parameter",
                    "void f(ArrayList<String>... xs) { }"),
            acceptedByBoth("a variable-arity parameter of a generic type",
                    "void f(Map<String, ArrayList<String>>... xs) { }"),
            acceptedByBoth("an array in a type argument",
                    "List<ArrayList<String>[]> f() { return null; }"),
            acceptedByBoth("an array of a type that holds one",
                    "Map<String, ArrayList<String>>[] f() { return null; }"),
            acceptedByBoth("a raw array",
                    "HashMap[] f() { return null; }"),
            acceptedByBoth("the lower bound of a wildcard",
                    "void f(List<? super HashSet<String>> sink) { }"),
            new Case("a type variable bounded by one",
                    inClass("<T extends ArrayList<String>> T f() { return null; }"), 1, 0),

            // What a record owns.
            acceptedByBoth("a method of a record",
                    "record R(int n) { ArrayList<String> values() { return null; } }"),
            acceptedByBoth("a parameter of a method of a record",
                    "record R(int n) { void with(ArrayList<String> x) { } }"),
            acceptedByBoth("a constructor of a record",
                    "record R(int n) { R(int n, ArrayList<String> more) { this(n); } }"),
            acceptedByBoth("a component of a record",
                    "record R(ArrayList<String> component) { }"),
            acceptedByBoth("a method of a record declared where it is used",
                    "void f() { record Local() { ArrayList<String> g() { return null; } } }"),
            refusedByBoth("a method of a class nested in a record",
                    "record R(int n) { static class Inner { ArrayList<String> g() { return null; } } }"),
            refusedByBoth("a method of an interface nested in a record",
                    "record R(int n) { interface Deep { ArrayList<String> d(); } }"),
            refusedByBoth("a method of an anonymous class made by a record",
                    "record R(int n) { Object o() { return new Object() { ArrayList<String> h() { return null; } }; } }"),

            // What a suppression stands for.
            acceptedByBoth("a method that suppresses it",
                    "@SuppressWarnings(\"NonApiType\") ArrayList<String> f() { return null; }"),
            acceptedByBoth("a parameter that suppresses it",
                    "void f(@SuppressWarnings(\"NonApiType\") HashMap<String, String> m) { }"),
            acceptedByBoth("a method that suppresses it among others",
                    "@SuppressWarnings({\"unused\", \"NonApiType\"}) ArrayList<String> f() { return null; }"),
            acceptedByBoth("a method that suppresses everything",
                    "@SuppressWarnings(\"all\") ArrayList<String> f() { return null; }"),
            acceptedByBoth("a method of a class that suppresses it",
                    "@SuppressWarnings(\"NonApiType\") static class Quiet { ArrayList<String> f() { return null; } }"),
            new Case("a class that suppresses it",
                    "@SuppressWarnings(\"NonApiType\")\nfinal class Fixture {\n"
                            + "    ArrayList<String> f() { return null; }\n"
                            + "    void g(HashMap<String, String> m) { }\n}", 0, 0),
            refusedByBoth("a method that suppresses something else",
                    "@SuppressWarnings(\"unused\") ArrayList<String> f() { return null; }"),
            refusedByBoth("the method beside one that suppresses it",
                    "@SuppressWarnings(\"NonApiType\") ArrayList<String> f() { return null; }\n"
                            + "    ArrayList<String> g() { return null; }"));

    @Test
    void whatTheHookRefusesIsNeverMoreThanErrorProneRefuses() {
        for (Case each : CASES) {
            assertTrue(each.hook() <= each.errorProne(), each.name()
                    + ": a hook that refuses more than CI stops a commit CI accepts");
        }
    }

    @Test
    void eachCaseIsRefusedAsManyTimesAsErrorProneAndTheHookEachSay(@TempDir Path dir)
            throws Exception {
        Map<Path, Case> filed = new LinkedHashMap<>();
        for (int i = 0; i < CASES.size(); i++) {
            Case each = CASES.get(i);
            Path file = dir.resolve("Fixture" + i + ".java");
            Files.writeString(file, """
                    import java.util.*;
                    import java.util.function.*;

                    %s
                    """.formatted(each.source().replace("Fixture", "Fixture" + i)));
            filed.put(file, each);
        }
        List<Path> files = List.copyOf(filed.keySet());

        Map<Path, Integer> byErrorProne = TheCommitHook.errorProneRefusals("NonApiType", dir, files);
        Map<Path, Integer> byTheHook = TheCommitHook.refusalsBy("MatchXpath", files);

        List<String> disagreements = new ArrayList<>();
        for (Map.Entry<Path, Case> each : filed.entrySet()) {
            Case expected = each.getValue();
            int errorProne = byErrorProne.getOrDefault(each.getKey(), 0);
            int hook = byTheHook.getOrDefault(each.getKey(), 0);
            if (errorProne != expected.errorProne() || hook != expected.hook()) {
                disagreements.add(expected.name() + ": Error Prone refused " + errorProne
                        + " (written " + expected.errorProne() + "), the hook refused " + hook
                        + " (written " + expected.hook() + ")");
            }
        }
        assertEquals(List.of(), disagreements);
    }
}
