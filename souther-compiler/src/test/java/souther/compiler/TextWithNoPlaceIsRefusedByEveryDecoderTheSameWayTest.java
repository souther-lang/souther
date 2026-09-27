package souther.compiler;

import net.unit8.raoh.Err;
import net.unit8.raoh.Issue;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Path;
import net.unit8.raoh.Result;
import souther.compiler.generated.JsonBoundary;
import souther.compiler.types.TextRule;
import souther.runtime.TextAdmission;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A decoder says an admission as a failure at the path (spec §what-a-string-holds), and the two
 * places that build one, a generated class and {@link JsonBoundary}, say it the same way.
 *
 * <p>Text with no place cannot be handed to a decoder here, since no test can build text longer than
 * the JVM's own bound, so what a decoder does with each admission is asked of the step that reads
 * one. Each refusal is Raoh's one code with a message of its own, at the path it was read at.
 */
class TextWithNoPlaceIsRefusedByEveryDecoderTheSameWayTest {

    private static final Path AT = Path.ROOT.append("s");

    private static final TextAdmission[] ADMISSIONS = {
            new TextAdmission.Admitted("a"), new TextAdmission.NotText(0), new TextAdmission.NoPlace()};

    private static Result<String> generated(TextAdmission admission) throws Exception {
        ClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data V = { s: String }
                """), TextWithNoPlaceIsRefusedByEveryDecoderTheSameWayTest.class.getClassLoader());
        Method text = Codecs.decoder(loader, "demo.V").getClass()
                .getDeclaredMethod("__text", TextAdmission.class, Path.class);
        text.setAccessible(true);
        @SuppressWarnings("unchecked")
        Result<String> result = (Result<String>) text.invoke(null, admission, AT);
        return result;
    }

    private static Issue issueOf(Result<String> result) {
        return assertInstanceOf(Err.class, result).issues().asList().get(0);
    }

    @Test
    void aGeneratedDecoderSaysWhatAnAdmissionWas() throws Exception {
        assertEquals(new Ok<>("a"), generated(ADMISSIONS[0]));
        Issue halfAPair = issueOf(generated(ADMISSIONS[1]));
        Issue noPlace = issueOf(generated(ADMISSIONS[2]));
        assertEquals(TextRule.REFUSED, halfAPair.code());
        assertEquals(TextRule.REFUSED, noPlace.code());
        assertEquals(TextRule.HALF_A_PAIR, halfAPair.message());
        assertEquals(TextRule.NO_PLACE, noPlace.message());
        assertEquals("/s", noPlace.path().toJsonPointer());
    }

    @Test
    void theRunnersReadingSaysItTheSameWay() throws Exception {
        for (TextAdmission admission : ADMISSIONS) {
            Result<String> generated = generated(admission);
            Result<String> read = JsonBoundary.textOf(admission, AT);
            if (generated instanceof Ok<String> ok) {
                assertEquals(ok, read);
            } else {
                Issue expected = issueOf(generated);
                Issue actual = issueOf(read);
                assertEquals(expected.code(), actual.code());
                assertEquals(expected.message(), actual.message());
                assertEquals(expected.path().toJsonPointer(), actual.path().toJsonPointer());
            }
        }
    }
}
