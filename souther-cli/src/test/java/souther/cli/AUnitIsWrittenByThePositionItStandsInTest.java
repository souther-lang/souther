package souther.cli;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * One unit, {@code Closed}, written in every position a unit crosses in. On its own and as a field
 * it writes its own form, the empty object; as a case of a sum with a field-bearing case the sum
 * puts the tag in that object; as a case of an enumeration the sum writes the case's name instead
 * (spec §encoder-derivation, §sum-discrimination). The four rows are the ones the specification's
 * example under §encoder-derivation writes, over the same declarations.
 *
 * <p>The positions are held together because the four answers are one rule read four times: the
 * unit's own form, and what the declared position adds to it. {@code Closed} is a case of both
 * sums, so the bare name cannot be the unit's own form without the discriminated sum disagreeing
 * with it.
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
            data Collected = { listed: List<Closed>, keyed: Map<String, Closed> }

            behavior alone : (c: Closed) -> Closed
            let alone (c) = c

            behavior held : (h: Holder) -> Holder
            let held (h) = h

            behavior gathered : (c: Collected) -> Collected
            let gathered (c) = c

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

    /** The element encoder a data's field hands a collection is the unit's own, so the element is
     *  the same empty object the unit writes on its own. */
    @Test
    void asAnElementOfAFieldsCollectionAUnitIsAnEmptyObject() throws Exception {
        String collected = "{\"listed\":[{},{}],\"keyed\":{\"k\":{}}}";
        assertEquals(collected, run("gathered", collected));
    }

    @Test
    void asACaseOfADiscriminatedSumAUnitIsItsTagAlone() throws Exception {
        assertEquals("{\"type\":\"Closed\"}", run("discriminated","{\"type\":\"Closed\"}"));
        assertEquals("{\"type\":\"Closed\"}", run("mixed", "0"));
    }

    @Test
    void asACaseOfAnEnumerationAUnitIsItsName() throws Exception {
        assertEquals("\"Closed\"", run("named","\"Closed\""));
        assertEquals("\"Closed\"", run("enumerated", "0"));
    }
}
