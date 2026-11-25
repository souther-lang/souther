package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two terms of a form that are written alike are two terms, and each is written with its weight:
 * how a term is written says how a reader is shown it, and not which term it is, so writing a form
 * out keeps every term it weighs whatever their names come to.
 */
class TwoTermsWrittenAlikeAreBothWrittenTest {

    /** A term written as {@code x}, whichever it is. */
    private record Written(int which) {

        @Override
        public String toString() {
            return "x";
        }
    }

    private static Map<Written, ExactRatio> twoWrittenAlike() {
        Map<Written, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(new Written(1), ExactRatio.ONE);
        coefs.put(new Written(2), ExactRatio.of(2));
        return coefs;
    }

    @Test
    void aFormAsAnAuthorWritesItWritesBoth() {
        String written = new LinearForm<>(ExactRatio.ZERO, twoWrittenAlike()).asAnAuthorWritesIt();
        assertEquals(List.of("2 * x", "x"),
                Arrays.stream(written.split(" \\+ ")).sorted().toList(), written);
    }

    @Test
    void theNamesAFormIsWrittenByAreOneForEachTerm() {
        List<Object> pieces = new LinearForm<>(ExactRatio.ZERO, twoWrittenAlike())
                .writtenAs(String::valueOf);
        assertEquals(2, pieces.stream().filter("x"::equals).count(), pieces::toString);
    }

    @Test
    void aCanonicalFormWritesBoth() {
        String written = new CanonicalForm<>(twoWrittenAlike()).toString();
        assertEquals(2, written.split(" \\+ ").length, written);
    }
}
