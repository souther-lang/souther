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
}
