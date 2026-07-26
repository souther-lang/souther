package example.inventory;

import net.unit8.raoh.Err;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Path;
import net.unit8.raoh.Result;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * Runs inventory.sou's {@code inspectBarcode} over the domain: a valid EAN-13 passes, a wrong check
 * digit is a scan error. This exercises the generated decode / apply / encode path (the check-digit
 * test is {@code List.indexedMap} + {@code List.sum} over the digits). The module's other behaviors
 * are checked by their {@code example}s at compile time.
 */
class InventoryTest {

    private Barcode barcode(String raw) {
        Result<Barcode> r = Barcode.decoder().decode(raw, Path.ROOT);
        if (r instanceof Err<Barcode> e) {
            throw new AssertionError("should decode: " + e.issues().asList());
        }
        return ((Ok<Barcode>) r).value();
    }

    @Test
    void aValidBarcodePassesInspection() {
        Object result = InspectBarcode.of().apply(barcode("9784873115658"));

        InspectionPassed passed = assertInstanceOf(InspectionPassed.class, result);
        assertEquals("9784873115658", InspectionPassed.encoder().encode(passed).get("code"));
    }

    @Test
    void aWrongCheckDigitIsAScanError() {
        assertInstanceOf(ScanError.class, InspectBarcode.of().apply(barcode("9784873115659")));
    }

    /** {@code baySlots} builds shelf codes rather than checking ones that came in: {@code List.range}
     *  gives the four levels of the bay and {@code String.padLeft} widens each number to the two
     *  digits {@code Location}'s invariant demands. */
    @Test
    void aBayNamesItsFourShelfCodes() {
        BayCandidates candidates = BaySlots.of().apply("A", 3L);

        assertEquals(java.util.List.of("A-03-01", "A-03-02", "A-03-03", "A-03-04"),
                BayCandidates.encoder().encode(candidates).get("locations"));
    }

    /** A bay number the format cannot hold is rejected where the code is built — the same invariant
     *  that rejects a malformed code arriving from outside. */
    @Test
    void aBayPastTheFormatIsRejectedAtConstruction() {
        org.junit.jupiter.api.Assertions.assertThrows(souther.runtime.ConstraintViolation.class,
                () -> BaySlots.of().apply("A", 100L));
    }
}
