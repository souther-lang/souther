package souther.compiler.examples;

import net.unit8.raoh.Ok;
import net.unit8.raoh.Path;
import net.unit8.raoh.decode.Decoder;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Symbols;
import souther.compiler.query.Compilation;
import souther.compiler.types.Type;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The envelope a value wears is the one the position reads it through, not one its case is owed
 * wherever it stands. A case's own Encoder writes no discriminator and its sum's writes one
 * (spec §encode-law), so the same {@code Approved} is {@code {"id":1}} where {@code Approved} is
 * declared and {@code {"id":1,"type":"Approved"}} where {@code Approved | Rejected} is.
 */
class AValueWearsTheEnvelopeThePositionReadsItThroughTest {

    private static final String MODULE = """
            module demo

            data Approved = { id: Int }
            data Rejected = { id: Int }
            data Decision = Approved | Rejected
            data Outcome = Approved | Rejected

            data Draft
            data Filed
            data Stage = Draft | Filed
            data Note = { text: String }
            data Step = Draft | Note

            data Yen = Int
            data Paid = Yen
            data Settlement = Paid | Draft
            """;

    private final Compilation compilation = compiled();
    private final Symbols symbols = compilation.symbols("demo");
    private final NeutralForm neutral = new NeutralForm(symbols);

    private static Compilation compiled() {
        Compilation c = Compilation.ofSource(MODULE, "Main");
        c.answerEverything();
        return c;
    }

    /** A value of {@code type}, as a helper would have answered with one: through its own decoder,
     *  which is the one place a case is built here without going through a sum. */
    @SuppressWarnings("unchecked")
    private Object value(String type, Object written) throws Exception {
        Decoder<Object, ?> decoder = (Decoder<Object, ?>) compilation.loader()
                .loadClass("demo." + type).getMethod("decoder").invoke(null);
        return ((Ok<?>) decoder.decode(written, Path.ROOT)).value();
    }

    private Object approved() throws Exception {
        return value("Approved", Map.of("id", 1L));
    }

    private Object unit(String type) throws Exception {
        return value(type, Map.of());
    }

    private Object paid() throws Exception {
        return value("Paid", 500L);
    }

    private Type at(String type) {
        return Type.ref(symbols.own(type));
    }

    @Test
    void aCaseAtItsOwnPositionCarriesNoDiscriminator() throws Exception {
        assertEquals(Map.of("id", 1L), neutral.of(approved(), at("Approved"), "h"));
    }

    @Test
    void aCaseAtASumThatListsItCarriesTheTagThatSumsDecoderReads() throws Exception {
        assertEquals(Map.of("id", 1L, "type", "Approved"),
                neutral.of(approved(), at("Decision"), "h"));
    }

    /** Two sums may list one case, and each position reads it through its own decoder. What they
     *  read it under agrees for as long as every discriminator is derived (issue #683). */
    @Test
    void eachSumThatListsTheCaseReadsItThroughItsOwnDecoder() throws Exception {
        assertEquals(neutral.of(approved(), at("Decision"), "h"),
                neutral.of(approved(), at("Outcome"), "h"));
    }

    /** A unit case travels as its bare name where the position is an enumeration, and wears the tag
     *  where the position is a sum that has a field-bearing case as well. */
    @Test
    void aUnitCaseIsANameAtAnEnumerationAndATagAtASumThatIsNotOne() throws Exception {
        assertEquals("Draft", neutral.of(unit("Draft"), at("Stage"), "h"));
        assertEquals(Map.of("type", "Draft"), neutral.of(unit("Draft"), at("Step"), "h"));
    }

    /** At its own type a unit case is read by its own decoder, which ignores what it is handed. */
    @Test
    void aUnitCaseAtItsOwnPositionCarriesNoDiscriminator() throws Exception {
        assertEquals(Map.of(), neutral.of(unit("Draft"), at("Draft"), "h"));
    }

    /** A newtype's form is its inner value where the position reads it as itself, and the inner
     *  value under `value` beside the tag where the position is a sum that lists it. */
    @Test
    void aNewtypeIsBareAtItsOwnPositionAndWrappedAtASumThatListsIt() throws Exception {
        assertEquals(500L, neutral.of(paid(), at("Paid"), "h"));
        assertEquals(Map.of("type", "Paid", "value", 500L),
                neutral.of(paid(), at("Settlement"), "h"));
    }

    /**
     * Where the position has no declared type — an answer of several types, which admission and not
     * a decoder decides — the sums that list the case answer instead. Held here because it is the
     * one thing the position cannot be asked for, and because it is right only for as long as every
     * discriminator is derived (issue #683).
     */
    @Test
    void aPositionWithNoDeclaredTypeIsAnsweredByTheSumsThatListTheCase() throws Exception {
        assertEquals(Map.of("id", 1L, "type", "Approved"), neutral.of(approved(), null, "h"));
        assertEquals(Map.of("type", "Draft"), neutral.of(unit("Draft"), null, "h"));
    }
}
