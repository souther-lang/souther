package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.compiler.ast.Hir;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Names;
import souther.lsp.analysis.SemanticProbe.Reading;
import souther.lsp.analysis.SemanticProbe.Repair;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A field list is wanted at {@code request.plannedCost.}, which is not a document that parses, so
 * the compiler is told nothing about the line it is being asked about. What answers is the line as
 * it stands now, finished off — never the last line that compiled, whose type would be a wrong
 * answer wearing the shape of a right one.
 */
class WhatIsAskedOfAHalfWrittenLineIsAskedOfWhatItSaysNowTest {

    private static final String URI = "file:///m.sou";

    private static final String HEAD = """
            module m

            data Cost = { value: Int }
            data Draft = { plannedCost: Cost }

            behavior submit : (request: Draft) -> Int
            let submit (request) = \
            """;

    /** The buffer mid-edit: a `.` with nothing after it yet. */
    private static final String HALF_WRITTEN = HEAD + "request.plannedCost.\n";

    @Test
    void aDocumentThatParsesIsNotRepaired() {
        String whole = HEAD + "request.plannedCost.value\n";
        assertNull(SemanticProbe.repair(whole, whole.length()),
                "there is nothing here the author has not finished");
    }

    @Test
    void aTrailingDotIsFinishedOffAndTheSourceBeforeItIsUntouched() {
        int cursor = HALF_WRITTEN.indexOf(".\n") + 1;
        Repair repair = SemanticProbe.repair(HALF_WRITTEN, cursor);

        assertNotNull(repair, "a `.` with nothing after it is what this is for");
        assertEquals(cursor, repair.firstInserted(), "the insertion begins at the cursor");
        assertEquals(HALF_WRITTEN.substring(0, cursor),
                repair.text().substring(0, repair.firstInserted()),
                "and everything before it is the source, character for character");
        assertTrue(repair.text().startsWith(HALF_WRITTEN.substring(0, cursor)),
                "nothing was deleted or replaced");
    }

    @Test
    void anUnclosedCallIsClosedAtTheEnd() {
        String calling = HEAD + "cost(request\n";
        Repair repair = SemanticProbe.repair(calling, calling.length());

        assertNotNull(repair, "a call whose bracket has not been typed yet");
        assertEquals(calling.length(), repair.firstInserted(),
                "the bracket goes at the end, so every offset in the source is where it was");
    }

    @Test
    void whatMayBeReadStopsWhereTheInsertionBegins() {
        Reading reading = probed(HALF_WRITTEN);
        Hir.FieldAccess written = accessOf(reading);

        assertTrue(reading.mayBeRead(written.target().region()),
                "`request.plannedCost` is the author's, and it is what a field list is taken from");
        assertFalse(reading.mayBeRead(written.region()),
                "and the access around it takes in the name the probe put there");
    }

    @Test
    void theReceiverIsReadFromTheTextThatIsThereNow() {
        // Edited from one field to another. What the last compiling source said about `address`
        // reaches nothing: the probe compiles what the buffer says, and the buffer says `amount`.
        String head = """
                module m

                data Address = { city: Text }
                data Amount = { units: Int }
                data Customer = { address: Address, amount: Amount }

                behavior f : (customer: Customer) -> Int
                let f (customer) = \
                """;
        Reading was = probed(head + "customer.address.\n");
        assertEquals("address", fieldOf(accessOf(was).target()));

        Reading now = probed(head + "customer.amount.\n");
        assertEquals("amount", fieldOf(accessOf(now).target()),
                "the receiver is the one written now");
    }

    /** The probe over a workspace of one document, with the buffer as it stands. */
    private static Reading probed(String text) {
        Map<String, String> joining = new LinkedHashMap<>();
        Reading reading = new SemanticProbe().of(joining, Set.of(), ModulePath.EMPTY, URI, text,
                text.indexOf(".\n") < 0 ? text.length() : text.lastIndexOf(".\n") + 1);
        assertNotNull(reading, "the half-written line is one this knows how to finish");
        return reading;
    }

    /** The `let`'s body, which every source here writes as one field taken off another. */
    private static Hir.FieldAccess accessOf(Reading reading) {
        Hir.Module module = reading.compilation().db()
                .ask(new Names.Resolved("m")).value();
        assertNotNull(module, "the repaired source resolves");
        for (Hir.FnDef fn : module.fns()) {
            if (fn.body() instanceof Hir.FnBody.Written(Hir.Expr expr)
                    && expr instanceof Hir.FieldAccess access) {
                return access;
            }
        }
        throw new AssertionError("the module has no `let` whose body is a field access");
    }

    private static String fieldOf(Hir.Expr expr) {
        return ((Hir.FieldAccess) expr).name().canonical();
    }
}
