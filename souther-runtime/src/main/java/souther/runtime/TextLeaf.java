package souther.runtime;

import net.unit8.raoh.Path;
import net.unit8.raoh.Result;

import java.util.Map;

/**
 * What a decoder's string leaf does with text that arrives, said once for every place that builds
 * one: a generated class and {@code souther run}'s own reading both call {@link #admit}, so a value
 * refused by one is refused the same way by the other.
 *
 * <p>Whether the text is a {@code String} is {@link Strings#admission}'s to say. Both ways it is not
 * are Raoh's {@code invalid_format}, the code for text whose content is not of the form its type
 * takes, each with a message of its own. A value that is not a string at all is Raoh's
 * {@code type_mismatch}, and that is not this.
 *
 * <p>One step and not a map followed by a refinement for each refusal: every text field, key and
 * element of a decoded value passes here, and a step of a decoder is a result built per value.
 */
public final class TextLeaf {

    private TextLeaf() {}

    public static final String REFUSED = "invalid_format";

    public static final String HALF_A_PAIR = "holds half of a surrogate pair, which is not a character";

    public static final String NO_PLACE = "is longer than a String holds once canonicalized";

    /** The canonical {@code String} the text is, or the failure at {@code path} saying why it is not
     *  one. */
    public static Result<String> admit(String text, Path path) {
        return answer(Strings.admission(text), path);
    }

    static Result<String> answer(TextAdmission admission, Path path) {
        return switch (admission) {
            case TextAdmission.Admitted a -> Result.ok(a.text());
            case TextAdmission.NotText _ -> Result.failCustom(path, REFUSED, HALF_A_PAIR, Map.of());
            case TextAdmission.NoPlace _ -> Result.failCustom(path, REFUSED, NO_PLACE, Map.of());
        };
    }
}
