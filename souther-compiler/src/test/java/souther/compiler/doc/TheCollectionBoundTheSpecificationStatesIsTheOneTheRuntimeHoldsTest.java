package souther.compiler.doc;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.List;
import java.util.regex.Pattern;

import org.junit.jupiter.api.Test;
import souther.runtime.Capacity;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The bound on what a {@code List}, a {@code Map} or a {@code Set} holds is written in the
 * specification and held by the run time, and it is a value of the language, so the two are one
 * number. A run time that held another would answer differently from the specification at exactly
 * the collections near the bound.
 */
class TheCollectionBoundTheSpecificationStatesIsTheOneTheRuntimeHoldsTest {

    private static final String SPEC = "/META-INF/souther/specification.adoc";
    private static final String ANCHOR = "[[what-a-collection-holds]]";
    private static final Pattern LONG_NUMBER = Pattern.compile("`\\+(\\d{6,})\\+`");

    @Test
    void theSpecificationStatesTheBoundTheRuntimeHolds() throws IOException {
        String stated = "`+" + Capacity.MOST_ELEMENTS + "+` elements";
        assertTrue(paragraph().contains(stated),
                "what-a-collection-holds does not state the bound as " + stated);
    }

    /** The number is stated in the paragraph once: a second, different one would be a bound the
     *  test above does not see. */
    @Test
    void theParagraphStatesNoOtherBound() throws IOException {
        List<String> stated = LONG_NUMBER.matcher(paragraph()).results()
                .map(m -> m.group(1)).toList();
        assertEquals(List.of(String.valueOf(Capacity.MOST_ELEMENTS)), stated);
    }

    private static String paragraph() throws IOException {
        try (InputStream in = TheCollectionBoundTheSpecificationStatesIsTheOneTheRuntimeHoldsTest.class
                .getResourceAsStream(SPEC)) {
            String adoc = new String(in.readAllBytes(), StandardCharsets.UTF_8);
            return adoc.lines().filter(line -> line.startsWith(ANCHOR)).findFirst().orElseThrow();
        }
    }
}
