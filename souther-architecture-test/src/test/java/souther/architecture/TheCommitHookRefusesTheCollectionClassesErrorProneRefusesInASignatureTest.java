package souther.architecture;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import souther.architecture.TheCommitHook.Filed;

import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the pre-commit hook says about {@code ArrayList}, {@code LinkedList}, {@code HashSet},
 * {@code LinkedHashSet}, {@code TreeSet}, {@code HashMap}, {@code LinkedHashMap} and
 * {@code TreeMap}, held against what Error Prone's NonApiType says of the same source.
 *
 * <p>The hook is the same question asked of a parser, and what it must never do is refuse what CI
 * accepts, because that stops a commit nothing is wrong with. So each case is a source, and what
 * Error Prone refuses in it is what it gives when it is run over it ({@link TheCommitHook}), not a
 * count read off its documentation or its source.
 *
 * <p>The hook may refuse less than Error Prone, and where it does the case says so: a type
 * variable's bound is something Error Prone reads and a parser cannot. It may not refuse more, and
 * every case is checked for that as well as for what it says.
 */
class TheCommitHookRefusesTheCollectionClassesErrorProneRefusesInASignatureTest {

    /** A case over the members of a class; {@code Fixture} in a source names the class the test
     *  files it under. */
    private static Filed refusedByBoth(String name, String members) {
        return Filed.refusedByBoth(name, inClass(members));
    }

    private static Filed acceptedByBoth(String name, String members) {
        return Filed.acceptedByBoth(name, inClass(members));
    }

    private static String inClass(String members) {
        return "final class Fixture {\n    " + members + "\n}";
    }

    private static final List<Filed> CASES = List.of(
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
            refusedByBoth("a method of the body of an enum constant and the one it implements",
                    "enum E { A { ArrayList<String> g() { return null; } }; abstract ArrayList<String> g(); }"),
            refusedByBoth("a method of an anonymous class",
                    "Object f() { return new Object() { ArrayList<String> g() { return null; } }; }"),
            refusedByBoth("two in one signature",
                    "HashSet<String> f(HashMap<String, String> m) { return null; }"),
            Filed.refusedByBoth("an override and what it overrides",
                    "interface Reads { LinkedList<String> all(); }\n"
                            + "final class Fixture implements Reads {\n"
                            + "    @Override public LinkedList<String> all() { return null; }\n"
                            + "}"),

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
            Filed.hookStandsAside("a type variable bounded by one",
                    inClass("<T extends ArrayList<String>> T f() { return null; }")),

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
            Filed.acceptedByBoth("a class that suppresses it",
                    "@SuppressWarnings(\"NonApiType\")\nfinal class Fixture {\n"
                            + "    ArrayList<String> f() { return null; }\n"
                            + "    void g(HashMap<String, String> m) { }\n}"),
            refusedByBoth("a method that suppresses something else",
                    "@SuppressWarnings(\"unused\") ArrayList<String> f() { return null; }"),
            refusedByBoth("the method beside one that suppresses it",
                    "@SuppressWarnings(\"NonApiType\") ArrayList<String> f() { return null; }\n"
                            + "    ArrayList<String> g() { return null; }"));

    @Test
    void theHookStandsToErrorProneAsEachCaseSays(@TempDir Path dir) throws Exception {
        assertEquals(List.of(), TheCommitHook.disagreements(dir, "NonApiType", "NonApiType",
                CASES, (i, source) -> """
                        import java.util.*;
                        import java.util.function.*;

                        %s
                        """.formatted(source.replace("Fixture", "Fixture" + i))));
    }
}
