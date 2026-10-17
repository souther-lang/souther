package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;

import java.util.List;

/**
 * What {@code String.codePoints} answers on a text written down: each code point a number written
 * where the call is.
 *
 * <p>One answer for every reader that writes such a list out. The discharge of a rule and the
 * reading of an input both pick an element of it, and two accounts of which numbers those are would
 * be a program read one way where it is checked and another where it is measured.
 *
 * <p>The same numbers in the same order as a run answers: the text is the one the source wrote,
 * canonicalized where it was read and holding no half of a pair, and each code point is one
 * number, however many UTF-16 units it takes.
 */
public final class WrittenCodePoints {

    private WrittenCodePoints() {
    }

    /** The code points of {@code text}, in order, each a number written at {@code call}. */
    public static List<Core> of(String text, SourcePos call) {
        return text.codePoints()
                .<Core>mapToObj(each -> new Core.Int(each, Type.INT, call))
                .toList();
    }
}
