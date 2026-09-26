package souther.compiler;

import net.unit8.raoh.Ok;
import net.unit8.raoh.Result;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The language has no value called {@code Raw} and reserves no such name, so a module that writes it
 * as a case of a sum without declaring it gets a unit data of that spelling, as it would for any
 * other undeclared case.
 */
class RawIsAnOrdinaryNameTest {

    @Test
    void anUndeclaredCaseSpelledRawIsAUnitDataOfTheModel() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data Amount = Int
                data High = { threshold: Amount }
                data Reason = High | Raw
                """), getClass().getClassLoader());

        Result<?> raw = Codecs.decode(loader, "demo.Reason", Map.of("type", "Raw"));
        assertTrue(raw instanceof Ok, String.valueOf(raw));
        assertEquals("demo.Raw", ((Ok<?>) raw).value().getClass().getName());
    }
}
