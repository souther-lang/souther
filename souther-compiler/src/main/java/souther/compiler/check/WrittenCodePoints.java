package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;

import java.util.List;

/**
 * What {@code String.codePoints} answers on a text written down: each code point a number written
 * where the call is.
 *
 * <p>Written out by {@link ElementsWrittenOut}, which every reader that writes a container out
 * walks.
 *
 * <p>The same numbers in the same order as a run answers: the text is the one the source wrote,
 * canonicalized where it was read and holding no half of a pair, and each code point is one
 * number, however many UTF-16 units it takes.
 */
public final class WrittenCodePoints {

    private WrittenCodePoints() {
    }

    /** The first {@code most} code points of {@code text}, or every one where it holds fewer, in
     *  order, each a number written at {@code call}. */
    public static List<Core> of(String text, int most, SourcePos call) {
        return text.codePoints().limit(most)
                .<Core>mapToObj(each -> new Core.Int(each, Type.INT, call))
                .toList();
    }
}
