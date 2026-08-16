package souther.compiler.diag;

import souther.compiler.source.SourceId;
import souther.compiler.diag.QuotedFrom;

import souther.compiler.check.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.query.Compilation;
import souther.compiler.query.Front;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A position says which source it was read from.
 *
 * <p>A line and a column are enough while one file is being read. They stop being enough the moment
 * writings from several files are gathered under one module — which is what an attached
 * {@code examples for} file is for — because after that nothing about a coordinate says which file
 * it came from, and what gets quoted is whatever happens to sit at those numbers in the file the
 * reader guessed at (issue #309).
 *
 * <p>These are about the position alone, so that a failure here is not mistaken for a failure in
 * what reads one. Where a report ends up being said is
 * {@code AMistakeInAnAttachedFileIsSaidOnThatFileTest}.
 */
class APositionKnowsItsFileTest {

    private static final String SOURCE = """
            module m exposing ( N )
            data N = { v: Int }
            """;

    private static Ast.Module parsedAs(String id, String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put(id, source);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), souther.compiler.meta.ModulePath.EMPTY);
        return c.db().ask(new Front.Parsed(new SourceId(id))).value().module();
    }

    @Test
    void aPositionParsedFromASourceNamesThatSource() {
        Ast.Module m = parsedAs("m.sou", SOURCE);

        assertEquals(new QuotedFrom.ASourceThisCompileHolds(new SourceId("m.sou")),
                m.defs().get(0).pos().quotedFrom(),
                "the `data` was read from m.sou, so that is what its position says");
    }

    @Test
    void everyPositionOfAParsedModuleNamesIt() {
        Ast.Module m = parsedAs("m.sou", SOURCE);

        assertTrue(m.pos().isIn(new SourceId("m.sou")));
        assertTrue(m.defs().stream().allMatch(d -> d.pos().isIn(new SourceId("m.sou"))),
                "one index made every position, so there is no part of the module it missed");
    }

    @Test
    void aPositionBuiltByHandNamesNoSource() {
        assertInstanceOf(QuotedFrom.TextItCannotName.class, new SourcePos(4, 7).quotedFrom(),
                "a caller with no source to name says so by naming none");
    }

    @Test
    void aRegionsEndIsInTheSameFileAsItsStart() {
        Region r = Region.ofWidth(new SourcePos(4, 7, new SourceId("m.sou")), 5);

        assertTrue(r.end().isIn(new SourceId("m.sou")), "a region does not leave the source it began in");
    }

    /**
     * Line 25 of two files is the same coordinate and is not the same place. The whole of issue #309
     * is what follows from treating the two as one, so a position that dropped its source from what
     * makes it itself would leave the bug expressible again — this time inside every set and map that
     * holds one.
     */
    @Test
    void theSameCoordinateInTwoFilesIsTwoPlaces() {
        assertNotEquals(new SourcePos(25, 16, new SourceId("shippingfee.sou")),
                new SourcePos(25, 16, new SourceId("shippingfee.examples.sou")));
    }

    @Test
    void theSameCoordinateInOneFileIsOnePlace() {
        assertEquals(new SourcePos(25, 16, new SourceId("shippingfee.sou")),
                new SourcePos(25, 16, new SourceId("shippingfee.sou")));
        assertEquals(new SourcePos(25, 16, new SourceId("shippingfee.sou")).hashCode(),
                new SourcePos(25, 16, new SourceId("shippingfee.sou")).hashCode());
    }

    /**
     * The standard library is not one of the sources a compile was handed, so a position in it has no
     * file this compile could quote. Naming none is how it says so, and what reads a report then falls
     * back to the module it is about.
     */
    @Test
    void aModuleReadOffThePathCarriesNoFileOfThisCompiles() {
        Hir.FnDef helper = Prelude.helpers().values().iterator().next();

        assertInstanceOf(QuotedFrom.TextItCannotShow.class, helper.pos().quotedFrom(),
                "the prelude is in no source of the compile that reads it");
    }

    /** A source id names a source or is absent. An empty one is neither, and would be a file nothing
     *  can be quoted from that nonetheless reads as an answer. */
    @Test
    void aBlankSourceIdIsRefused() {
        assertThrows(IllegalArgumentException.class, () -> new SourcePos(1, 1, new SourceId("")));
        assertThrows(IllegalArgumentException.class, () -> new SourcePos(1, 1, new SourceId("  ")));
    }
}
