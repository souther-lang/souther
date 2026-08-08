package souther.compiler;

import net.unit8.raoh.Err;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Result;

import org.jooq.Field;
import org.jooq.Record;
import org.jooq.SQLDialect;
import org.jooq.impl.DSL;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A sum's decoder takes a wrapped case's contents out of {@code "value"} and hands them over, so what
 * reads them is the decoder for what they are — a column's value is no longer a row, and an object's
 * field value is no longer that object. Which decoder that is, is the question a field of a data
 * already asks, and the answer is the same one.
 */
class ACaseIsReadByTheDecoderForWhatItIsHandedTest {

    private static final String OVER_A_COLUMN = """
            module demo

            data Code = String
            data Rec = { x: Int }
            data S = Code | Rec
            """;

    private static final String OVER_AN_OBJECT = """
            module demo

            data Inner = { x: Int }
            data OverRec = Inner
            data Other = { y: Int }
            data S = OverRec | Other
            """;

    private BytesClassLoader compile(String module) {
        return new BytesClassLoader(Compiler.compile(module), getClass().getClassLoader());
    }

    /** A jOOQ row is flat: the value under the envelope key is a column, and a column is read by the
     *  newtype's own decoder — the one a flat row's newtype field is read by. */
    @Test
    void aWrappedCaseOfARowIsReadFromItsColumn() throws Exception {
        Field<String> type = DSL.field(DSL.name("type"), String.class);
        Field<String> value = DSL.field(DSL.name("value"), String.class);
        Record row = DSL.using(SQLDialect.DEFAULT).newRecord(type, value);
        row.set(type, "Code");
        row.set(value, "x");

        Result<?> r = Codecs.decode(compile(OVER_A_COLUMN), "demo.S", "recordDecoder", row);

        assertInstanceOf(Ok.class, r, String.valueOf(r));
        assertEquals("demo.Code", ((Ok<?>) r).value().getClass().getName());
    }

    /** A newtype over a data reads an object, so what is under the envelope key is asked to be one —
     *  and a value that is not says so at that key, rather than arriving inside the case's decoder. */
    @Test
    void aWrappedCaseOverAnObjectSaysSoWhenTheValueIsNotOne() throws Exception {
        Result<?> r = Codecs.decode(compile(OVER_AN_OBJECT), "demo.S",
                Map.of("type", "OverRec", "value", "not an object"));

        assertInstanceOf(Err.class, r, String.valueOf(r));
        assertEquals("/value", ((Err<?>) r).issues().asList().get(0).path().toString());
        assertEquals("type_mismatch", ((Err<?>) r).issues().asList().get(0).code());
    }
}
