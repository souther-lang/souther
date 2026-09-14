package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Located;
import souther.compiler.diag.msg.NameMessage;
import souther.compiler.source.SourceId;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A declaration nobody could derive a boundary representation for costs the readers that name it,
 * and no others.
 *
 * <p>Four shapes, and they are the corners of one rule. Within a module, what is wrong with one
 * declaration leaves the definitions beside it read. Across modules, a module that reads a
 * declaration that did not come out reads it as the declaration it is — its fields are what they
 * are, and the module that wrote it is the module that wrote it — so it is not told a second time
 * that something is wrong, and it is not told something false either. A module that reads nothing
 * of the kind goes on as though nothing had happened, because nothing has.
 *
 * <p>Held over what a compile says rather than over which query answered, so that the rule survives
 * the queries being rearranged: what an author reads is the list of reports, and that is what is
 * asserted.
 */
class WhatOneModuleCouldNotDeriveCostsTheReadersThatNameItTest {

    private static Map<SourceId, List<Diagnostic>> diagnose(String... sources) {
        Map<String, String> byId = new LinkedHashMap<>();
        for (int i = 0; i < sources.length; i++) {
            byId.put("s" + i + ".sou", sources[i]);
        }
        return Located.diagnosticsOf(Compiler.diagnoseModules(byId, Set.of()));
    }

    private static List<Diagnostic> of(Map<SourceId, List<Diagnostic>> found, int source) {
        return found.get(new SourceId("s" + source + ".sou"));
    }

    /**
     * A declaration of this module could not be derived, and the definitions beside it are read.
     *
     * <p>Two reports and not one: the name that denotes nothing, and the mistake in a body that has
     * nothing to do with it. Read as one, a module would go unchecked from its first bad
     * declaration onwards, and an author fixing that name would meet the next mistake only after.
     */
    @Test
    void aDeclarationOfThisModuleThatDidNotComeOutLeavesTheOthersRead() {
        List<Diagnostic> found = of(diagnose("""
                module m.a exposing ( A, g )

                data A = { value: Nowhere }

                behavior g : (n: Int) -> Int
                let g (n) = "not an Int"
                """), 0);

        assertEquals(2, found.size(), "the unknown name, and g's own mistake: " + found);
        assertTrue(found.stream().anyMatch(d -> d.said() instanceof NameMessage.NoTypeOfThatName),
                "the name that denotes nothing: " + found);
        assertTrue(found.stream().anyMatch(d -> d.diff() != null),
                "and the type mismatch in the definition that has one: " + found);
    }

    /** A module that imports one is not told about it a second time. */
    @Test
    void aModuleThatImportsOneIsNotToldAgain() {
        Map<SourceId, List<Diagnostic>> found = diagnose("""
                module lib exposing ( N )
                data N = { v: Nowhere }
                """, """
                module reads
                import lib ( N )
                behavior g : (n: N) -> N
                let g (n) = n
                """);

        assertEquals(1, of(found, 0).size(), "the module that wrote it says what is wrong");
        assertEquals(List.of(), of(found, 1), "and the one that reads it says nothing");
    }

    /** Nor is a module two imports away. */
    @Test
    void norIsAModuleTwoImportsAway() {
        Map<SourceId, List<Diagnostic>> found = diagnose("""
                module deep exposing ( N )
                data N = { v: Nowhere }
                """, """
                module mid exposing ( M )
                import deep ( N )
                data M = { n: N }
                """, """
                module far
                import mid ( M )
                behavior g : (m: M) -> M
                let g (m) = m
                """);

        assertEquals(1, of(found, 0).size(), "the module that wrote it says what is wrong");
        assertEquals(List.of(), of(found, 1), "the one that reads it says nothing");
        assertEquals(List.of(), of(found, 2), "and neither does the one that reads that");
    }

    /** And a module that names none of it is read as though nothing had happened. */
    @Test
    void aModuleThatNamesNoneOfItIsReadAsEver() {
        Map<SourceId, List<Diagnostic>> found = diagnose("""
                module broken exposing ( N )
                data N = { v: Nowhere }
                """, """
                module apart exposing ( P )
                data P = { n: Int }
                behavior g : (p: P) -> Int
                let g (p) = "not an Int"
                """);

        assertEquals(1, of(found, 0).size(), "the broken module says what is wrong");
        assertEquals(1, of(found, 1).size(),
                "and the one beside it is read for its own mistake: " + of(found, 1));
        assertTrue(of(found, 1).get(0).diff() != null,
                "which is the type mismatch it wrote: " + of(found, 1));
    }
}
