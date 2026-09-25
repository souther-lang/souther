package souther.compiler.sites;

import souther.compiler.ast.Hir;
import souther.compiler.diag.Region;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Names;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What an editor offers after {@code lib.}, in the order a reader of {@code lib} meets it: the order
 * its {@code exposing} clause writes the names in, and where it writes no clause, the order its
 * declarations are written in, whatever kind each is.
 */
class WhatAModuleOffersIsListedInTheOrderItIsWrittenTest {

    private static final String DECLARATIONS = """

            let first = 1
            data Second = { n: Int }
            behavior third : (s: Second) -> Int
            let third (s) = s.n
            let fourth (n: Int) : Int = n + first
            """;

    @Test
    void aModuleWritingNoClauseIsOfferedInTheOrderItsDeclarationsAreWritten() {
        assertEquals(List.of("first", "Second", "third", "fourth"),
                offeredBy("module lib\n" + DECLARATIONS));
    }

    @Test
    void aModuleWritingAClauseIsOfferedInTheOrderTheClauseWritesThem() {
        assertEquals(List.of("fourth", "Second"),
                offeredBy("module lib exposing ( fourth, Second )\n" + DECLARATIONS));
    }

    private static List<String> offeredBy(String lib) {
        Compilation compilation = Compilation.ofSources(List.of(lib), ModulePath.EMPTY);
        Hir.Module resolved = compilation.db().ask(new Names.Resolved("lib")).value();
        SemanticSnapshot snapshot = SemanticSnapshot.of(compilation.db(), "lib")
                .orElseThrow(() -> new AssertionError("lib has a snapshot"));
        return snapshot.namesIn(new MemberReceiver.Namespace.OfModule("lib",
                        Region.point(resolved.pos())))
                .stream().map(Published::name).toList();
    }
}
