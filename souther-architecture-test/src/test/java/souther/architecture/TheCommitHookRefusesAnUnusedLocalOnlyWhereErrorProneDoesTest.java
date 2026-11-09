package souther.architecture;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import souther.architecture.TheCommitHook.Filed;

import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static souther.architecture.TheCommitHook.Filed.acceptedByBoth;
import static souther.architecture.TheCommitHook.Filed.refusedByBoth;

/**
 * What the pre-commit hook says about a local that nothing reads, held against what Error Prone's
 * UnusedVariable says of the same source.
 *
 * <p>Checkstyle's UnusedLocalVariable reads more than Error Prone does. Error Prone lets a local
 * stand when its name is {@code ignored}, begins with {@code unused} or is {@code _}, and it reads
 * a binding only where {@code x instanceof T name} introduces it, not where a switch case or a
 * record pattern does. A rule that read them would stop a commit CI accepts, so the hook's rule
 * stands aside for them, and each of those edges is a case here, held to what Error Prone gives
 * when it is run over it ({@link TheCommitHook}).
 */
class TheCommitHookRefusesAnUnusedLocalOnlyWhereErrorProneDoesTest {

    /** Each case is the members of a class. */
    private static final List<Filed> CASES = List.of(
            // What nothing reads.
            refusedByBoth("a local that is never read",
                    "void f() { int foo = 1; }"),
            refusedByBoth("two of them", "void f() { int a = 1; int b = 2; }"),
            refusedByBoth("a variable of a for-each loop",
                    "void f(List<String> xs) { for (String y : xs) { } }"),
            refusedByBoth("a local that is only assigned",
                    "void f() { int w; w = 5; }"),
            refusedByBoth("a local in a lambda",
                    "void f() { Runnable r = () -> { int z = 2; }; r.run(); }"),
            refusedByBoth("a local in a method of a local class",
                    "void f() { class Loc { int g() { int z = 1; return 2; } } }"),
            refusedByBoth("a local that a for loop declares beside the one it uses",
                    "void f() { for (int i = 0, j = 1; i < 3; i++) { } }"),
            refusedByBoth("a binding that instanceof introduces",
                    "boolean f(Object o) { return o instanceof String s; }"),

            // What is read.
            acceptedByBoth("a local read in a lambda",
                    "void f() { int q = 1; Runnable r = () -> System.out.println(q); r.run(); }"),
            acceptedByBoth("a binding read after the condition that introduced it",
                    "int f(Object o) { if (!(o instanceof String s)) { return 0; } return s.length(); }"),

            // What Error Prone lets stand by its name.
            acceptedByBoth("a local named ignored",
                    "void f() { int ignored = 1; }"),
            acceptedByBoth("a local whose name begins with unused",
                    "void f() { int unusedThing = 1; }"),
            acceptedByBoth("a local with no name",
                    "void f() { int _ = 1; }"),
            acceptedByBoth("a binding of instanceof named ignored",
                    "boolean f(Object o) { return o instanceof String ignored; }"),
            acceptedByBoth("a binding of instanceof whose name begins with unused",
                    "boolean f(Object o) { return o instanceof String unusedS; }"),
            acceptedByBoth("a binding of a switch case named ignored",
                    "int f(Opt o) { return switch (o) { case None ignored -> 1; case Some _ -> 2; }; }"),

            // What Error Prone does not read.
            acceptedByBoth("the resource of a try",
                    "void f() throws Exception { try (var r = new java.io.StringReader(\"\")) { } }"),
            acceptedByBoth("the parameter of a catch",
                    "void f() { try { } catch (RuntimeException e) { } }"),
            acceptedByBoth("a component of a record pattern in instanceof",
                    "boolean f(Opt o) { return o instanceof Some(String v); }"),
            acceptedByBoth("a component of a record pattern in a record pattern",
                    "boolean f(Holder h) { return h.o() instanceof Some(String v); }"),
            acceptedByBoth("a component of a record pattern that a condition introduces for the rest of the method",
                    "Optional<String> f(Holder h) {\n"
                            + "        if (h == null || !(h.o() instanceof Some(String in))) {\n"
                            + "            return Optional.empty();\n"
                            + "        }\n"
                            + "        return Optional.of(\"x\");\n"
                            + "    }"),
            acceptedByBoth("a binding of a switch case",
                    "int f(Opt o) { return switch (o) { case None n -> 1; case Some s -> 2; }; }"),
            acceptedByBoth("a component of a record pattern in a switch case",
                    "int f(Opt o) { return switch (o) { case None _ -> 1; case Some(String v) -> 2; }; }"));

    private static String inClass(String members) {
        return """
                final class Fixture {
                    sealed interface Opt permits None, Some { }
                    record None() implements Opt { }
                    record Some(String v) implements Opt { }
                    record Holder(Opt o) { }
                    %s
                }
                """.formatted(members);
    }

    @Test
    void theHookStandsToErrorProneAsEachCaseSays(@TempDir Path dir) throws Exception {
        assertEquals(List.of(), TheCommitHook.disagreements(dir, "UnusedVariable",
                "UnusedLocalVariable", CASES, (i, members) -> "import java.util.*;\n\n"
                        + inClass(members).replace("Fixture", "Fixture" + i)));
    }
}
