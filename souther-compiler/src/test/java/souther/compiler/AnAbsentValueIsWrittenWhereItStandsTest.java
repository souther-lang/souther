package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.DataMessage;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Absence has one form wherever it stands. A field holds it by not being there; an element and a
 * map's value have no key to omit, so there it is written {@code null}. What the two share is that
 * absence reads back as the absence it was written from, so a value carrying one round-trips.
 */
class AnAbsentValueIsWrittenWhereItStandsTest {

    private static ClassLoader compiled(String src) throws Exception {
        return new BytesClassLoader(Compiler.compile(src),
                AnAbsentValueIsWrittenWhereItStandsTest.class.getClassLoader());
    }

    private static Diagnostic diagnosticOf(String src) {
        return assertThrows(CompileException.class, () -> Compiler.compile(src)).diagnostic();
    }

    /** Decodes {@code raw} into {@code demo.Hold} and encodes the value straight back out. */
    private static Object roundTrip(String fieldType, Object raw) throws Exception {
        ClassLoader loader = compiled("module demo\ndata Hold = { xs: " + fieldType + " }\n");
        return Codecs.encode(loader, "demo.Hold", Codecs.decoded(loader, "demo.Hold", Map.of("xs", raw)));
    }

    private static List<Object> listOf(Object... members) {
        List<Object> out = new ArrayList<>();
        for (Object m : members) {
            out.add(m);
        }
        return out;
    }

    private static Map<String, Object> mapOf(String k1, Object v1, String k2, Object v2) {
        Map<String, Object> out = new LinkedHashMap<>();
        out.put(k1, v1);
        out.put(k2, v2);
        return out;
    }

    @Test
    void anAbsentListElementIsWrittenAsNull() throws Exception {
        assertEquals(Map.of("xs", listOf(1L, null, 3L)),
                roundTrip("List<Option<Int>>", listOf(1L, null, 3L)));
    }

    @Test
    void anAbsentMapValueIsWrittenAsNullRatherThanDroppingTheKey() throws Exception {
        assertEquals(Map.of("xs", mapOf("a", 1L, "b", null)),
                roundTrip("Map<String, Option<Int>>", mapOf("a", 1L, "b", null)));
    }

    // A Set writes its members in ascending order of their external representation, where null is
    // first (spec [#collections]). That order is the whole of what a Set's array says, so the input
    // is given out of order to show the encoder decides it.
    @Test
    void anAbsentSetMemberSortsBeforeEveryValue() throws Exception {
        assertEquals(Map.of("xs", listOf(null, 1L, 2L)),
                roundTrip("Set<Option<Int>>", listOf(2L, null, 1L)));
    }

    @Test
    void anAbsentElementOfANestedCollectionIsWrittenAsNull() throws Exception {
        assertEquals(Map.of("xs", listOf(listOf(1L, null), listOf())),
                roundTrip("List<List<Option<Int>>>", listOf(listOf(1L, null), listOf())));
    }

    // A field keeps the form it had: absence is the key not being there, which is what the round
    // trip reads back (spec [#encoder-derivation]).
    @Test
    void anAbsentFieldIsStillTheKeyNotBeingThere() throws Exception {
        ClassLoader loader = compiled("module demo\ndata Hold = { xs: Int?, n: Int }\n");
        assertEquals(Map.of("n", 7L),
                Codecs.encode(loader, "demo.Hold", Codecs.decoded(loader, "demo.Hold", Map.of("n", 7L))));
    }

    // Absence has one form, so an optional holding an optional has two forms for three values and
    // no external representation (spec [#what-has-no-external-representation]). It is refused where
    // one is required, and refused as a diagnostic — reaching the backend with it was an internal
    // error escaping to the author.
    @Test
    void anOptionalUnderAnOptionalIsRefusedOnAField() {
        Diagnostic d = diagnosticOf("module demo\ndata Hold = { xs: Option<Option<Int>> }\n");
        assertInstanceOf(DataMessage.NoCodecCanBeDerived.class, d.said());
    }

    @Test
    void anOptionalUnderAnOptionalIsRefusedInsideACollection() {
        Diagnostic d = diagnosticOf("module demo\ndata Hold = { xs: List<Option<Option<Int>>> }\n");
        assertInstanceOf(DataMessage.NoCodecCanBeDerived.class, d.said());
    }

    // `?` marks where an optional is made and is written on a whole type only, so an optional inside
    // another type is named `Option<T>` (spec [#an-optional-is-not-written-inside-another-type]).
    // A message spelling it `Int??` or `Option<Int>?` would name a form the author cannot write.
    @Test
    void aRefusedNestedOptionalIsNamedTheWayItIsWritten() {
        Diagnostic d = diagnosticOf("module demo\ndata Hold = { xs: List<Option<Option<Int>>> }\n");
        assertEquals("Option<Option<Int>>",
                ((DataMessage.NoCodecCanBeDerived) d.said()).carries());
    }

    @Test
    void aRefusedOptionalUnderAnOptionalOnAFieldIsNamedTheSameWay() {
        Diagnostic d = diagnosticOf("module demo\ndata Hold = { xs: Option<Option<Int>> }\n");
        assertEquals("Option<Option<Int>>",
                ((DataMessage.NoCodecCanBeDerived) d.said()).carries());
    }

    // A helper's signature is not a codec boundary, so none of this is asked of it.
    @Test
    void aHelperSignatureTakesAnOptionalUnderAnOptional() throws Exception {
        compiled("""
                module demo
                data R = { n: Int }
                let depth (v: Option<Option<Int>>) : Int = 1
                """);
    }
}
