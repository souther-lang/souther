package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The standard library implements some of what it publishes with helpers of its own — `List.fold`
 * walks the list through `foldFrom`, which takes the index the sugar supplies. Those are not part of
 * the surface a caller writes against: reachable or not is what makes a name public, so the
 * declaration says which it is, and everything outside the reserved namespace is told the library
 * has no such member.
 */
class APrivateDeclarationIsNotPublishedTest {

    private static final String MODULE = """
            module demo

            data Counted = { n: Int }

            behavior tally : (xs: List<Int>) -> Counted
                constructs Counted

            let tally (xs) = Counted { n = %s }
            """;

    private static CompileException rejects(String expr) {
        return assertThrows(CompileException.class, () -> Compiler.compile(MODULE.formatted(expr)));
    }

    @Test
    void theLibraryStillReachesItsOwnPrivateHelper() {
        // `List.fold` is sugar for `foldFrom`, so a module that folds proves the private helper is
        // reachable from inside the library even though no caller can name it.
        Compiler.compile(MODULE.formatted("List.fold((acc, x) -> acc + x, 0, xs)"));
    }

    @Test
    void aCallerIsToldTheLibraryHasNoSuchMember() {
        CompileException e = rejects("List.foldFrom((acc, x) -> acc + x, 0, xs, 0)");

        String message = e.getMessage();
        assertTrue(message.contains("List.foldFrom"), message);
        assertTrue(message.contains("not a standard-library function"), message);
    }

    @Test
    void itIsRefusedHandedOverByNameToo() {
        CompileException e = rejects("List.fold(List.foldFrom, 0, xs)");

        assertTrue(e.getMessage().contains("List.foldFrom"), e.getMessage());
    }

    @Test
    void aPrivateNameIsNotOfferedAsAHintForABareOne() {
        // A bare `foldFrom` gets the ordinary unknown-identifier report, not "did you mean
        // `List.foldFrom`" — a hint naming a member no one may write is worse than none.
        CompileException e = rejects("foldFrom((acc, x) -> acc + x, 0, xs, 0)");

        assertFalse(e.getMessage().contains("List.foldFrom"), e.getMessage());
    }

    @Test
    void privateIsACorePrivilege() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Counted = { n: Int }

                behavior tally : (xs: List<Int>) -> Counted
                    constructs Counted

                private let double (n: Int) = n * 2
                let tally (xs) = Counted { n = double(1) }
                """));

        assertTrue(e.getMessage().contains("`private` is a core privilege"), e.getMessage());
    }

    @Test
    void privateIsStillAnOrdinaryWordEverywhereElse() {
        // A soft keyword: only the word directly before a `let` is the modifier, so a field or a
        // parameter may still be called `private`.
        Compiler.compile("""
                module demo

                data Flag = { private: Bool }
                data Out = { n: Int }

                behavior read : (f: Flag) -> Out
                    constructs Out

                let read (f) = Out { n = if f.private then 1 else 0 }
                """);
    }

    @Test
    void thePublishedSurfaceLeavesThePrivateDeclarationsOut() {
        assertTrue(Prelude.entries().containsKey("List.foldFrom"));
        assertTrue(Prelude.isPrivateMember("List.foldFrom"));
        assertFalse(Prelude.published().contains("List.foldFrom"));
        assertTrue(Prelude.published().contains("List.fold"));
        assertEquals(Prelude.entries().size() - 1 + 1,   // one private out, the `List.fold` sugar in
                Prelude.published().size());
    }
}
