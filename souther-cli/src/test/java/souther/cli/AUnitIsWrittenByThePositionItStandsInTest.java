package souther.cli;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * One unit, {@code Closed}, written in the positions spec §encoder-derivation names for it. Wherever
 * the unit is the declared type — a behavior's input or output, a field, a {@code List} or
 * {@code Set} element, a {@code Map} value, at any depth and as an optional's present value — it
 * writes its own form, the empty object. As a case of a sum with a field-bearing case the sum puts
 * the tag in that object, and as a case of an enumeration the sum writes the case's name instead
 * (spec §sum-discrimination). The standalone, field and case rows are the specification's example
 * under §encoder-derivation, over the same declarations.
 *
 * <p>The positions are held together because the answers are one rule: the unit's own form, and
 * what the declared position adds to it. {@code Closed} is a case of both sums, so the bare name
 * cannot be the unit's own form without the discriminated sum disagreeing with it.
 */
class AUnitIsWrittenByThePositionItStandsInTest {

    @TempDir
    Path dir;

    private static final String MODEL = """
            module demo

            data Closed
            data Open = { since: Int }
            data Door = Open | Closed
            data Phase = Pending | Closed
            data Holder = { state: Closed }
            data Collected = {
                listed: List<Closed>
                , kept: Set<Closed>
                , keyed: Map<String, Closed>
                , nested: List<List<Closed>>
                , maybe: Closed?
                , gaps: List<Option<Closed>>
            }

            behavior alone : (c: Closed) -> Closed
            let alone (c) = c

            behavior held : (h: Holder) -> Holder
            let held (h) = h

            behavior gathered : (c: Collected) -> Collected
            let gathered (c) = c

            behavior counted : (xs: List<Closed>) -> List<Closed>
            let counted (xs) = xs

            behavior discriminated : (d: Door) -> Door
            let discriminated (d) = d

            behavior named : (p: Phase) -> Phase
            let named (p) = p

            behavior mixed : (n: Int) -> Open | Closed
                constructs Open
            let mixed (n) = if n > 0 then Open { since = n } else Closed

            behavior enumerated : (n: Int) -> Pending | Closed
            let enumerated (n) = if n > 0 then Pending else Closed
            """;

    private String run(String behavior, String input) throws Exception {
        Path file = dir.resolve("demo.sou");
        Files.writeString(file, MODEL);
        return Runner.run(file, behavior, input).trim();
    }

    @Test
    void onItsOwnAUnitIsAnEmptyObject() throws Exception {
        assertEquals("{}", run("alone", "{}"));
    }

    @Test
    void asAFieldAUnitIsAnEmptyObject() throws Exception {
        assertEquals("{\"state\":{}}", run("held", "{\"state\":{}}"));
    }

    /** The element encoder a field hands a collection is the unit's own, so every element — at any
     *  depth, and an optional element that is present — is the empty object the unit writes on its
     *  own, while an absent one is {@code null} as it is for any element. */
    @Test
    void asTheElementOfAFieldsCollectionAUnitIsAnEmptyObject() throws Exception {
        String collected = "{\"listed\":[{},{}],\"kept\":[{}],\"keyed\":{\"k\":{}},"
                + "\"nested\":[[{}]],\"maybe\":{},\"gaps\":[{},null]}";
        assertEquals(collected, run("gathered", collected));
    }

    @Test
    void asTheElementOfABehaviorsListAUnitIsAnEmptyObject() throws Exception {
        assertEquals("[{},{}]", run("counted", "[{},{}]"));
    }

    @Test
    void asACaseOfADiscriminatedSumAUnitIsItsTagAlone() throws Exception {
        assertEquals("{\"type\":\"Closed\"}", run("discriminated", "{\"type\":\"Closed\"}"));
        assertEquals("{\"type\":\"Closed\"}", run("mixed", "0"));
    }

    @Test
    void asACaseOfAnEnumerationAUnitIsItsName() throws Exception {
        assertEquals("\"Closed\"", run("named", "\"Closed\""));
        assertEquals("\"Closed\"", run("enumerated", "0"));
    }
}
