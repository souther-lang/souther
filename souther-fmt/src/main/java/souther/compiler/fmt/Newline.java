package souther.compiler.fmt;

import java.util.List;

/**
 * A break the layout wrote: where it is, how far in the line after it starts, and the nestings it
 * was written under, outermost first.
 *
 * <p>The nestings are named rather than measured. The indentation rule answers about a pair of
 * consecutive levels, and a written indent of eight says only what the second of the two came to —
 * a formatter indenting the first level by four and the second by six writes the same eight.
 */
record Newline(int offset, int indent, List<Doc.NestRef> under) {

    Newline {
        under = List.copyOf(under);
    }
}
