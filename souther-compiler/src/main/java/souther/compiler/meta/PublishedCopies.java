package souther.compiler.meta;

import souther.compiler.copied.CopyRecord;
import souther.compiler.copied.CopyTarget;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.SortedMap;
import java.util.TreeMap;

/**
 * Copies as {@link ModuleMetadata} writes them and {@link ModuleReadback} reads them: one entry per
 * declaration, holding its kind, its module, its name, the form it is copied in and what it is
 * copied as, every part counted the way {@link PublishedLinkages} counts one.
 *
 * <p>Written in the order of the declarations, so one set of copies is one set of entries.
 */
public final class PublishedCopies {

    private PublishedCopies() {}

    /** The most bytes one string of an annotation may take: what a class file's UTF-8 constant
     *  holds. */
    private static final long LONGEST_UTF8_CONSTANT = 0xFFFF;

    /**
     * Whether the entry recording {@code target} as a constant written in {@code contentChars}
     * characters and {@code contentBytes} bytes of modified UTF-8 is one a class file can hold,
     * worked out from what the entry would be without writing it.
     *
     * <p>Asked before the constant's text is made. A decimal's text is as long as its scale is far
     * from nought, so one a few bytes wide can be a text nothing holds, and making it is what
     * fails. What does not fit is a copy with no constant to be recorded as, and is recorded as
     * what computes it.
     *
     * <p>The entry as {@link #written} writes it, counted the way a class file counts a string: in
     * the bytes of its modified UTF-8, each of the five parts led by its length in characters.
     */
    public static boolean constantFits(CopyTarget target, long contentChars, long contentBytes) {
        long bytes = counted(target.kind()) + counted(target.module()) + counted(target.name())
                + counted(CopyRecord.Form.CONSTANT.written());
        return bytes + String.valueOf(contentChars).length() + 1 + contentBytes
                <= LONGEST_UTF8_CONSTANT;
    }

    /** What {@link PublishedRequirements#counted(String)} writes of {@code text}, in bytes. */
    private static long counted(String text) {
        return String.valueOf(text.length()).length() + 1 + modifiedUtf8Length(text);
    }

    private static long modifiedUtf8Length(String text) {
        long bytes = 0;
        for (int at = 0; at < text.length(); at++) {
            char each = text.charAt(at);
            bytes += each == 0 ? 2 : each < 0x80 ? 1 : each < 0x800 ? 2 : 3;
        }
        return bytes;
    }

    static List<String> written(Map<CopyTarget, CopyRecord> copies) {
        List<String> out = new ArrayList<>(copies.size());
        new TreeMap<>(copies).forEach((target, record) -> out.add(
                PublishedRequirements.counted(target.kind())
                        + PublishedRequirements.counted(target.module())
                        + PublishedRequirements.counted(target.name())
                        + PublishedRequirements.counted(record.form().written())
                        + PublishedRequirements.counted(record.content())));
        return out;
    }

    /** The copies {@code entries} record, by the declaration — or null where one of them is not an
     *  entry this writes. */
    static SortedMap<CopyTarget, CopyRecord> read(List<String> entries) {
        SortedMap<CopyTarget, CopyRecord> out = new TreeMap<>();
        for (String entry : entries) {
            int[] at = {0};
            String kind = PublishedRequirements.counted(entry, at);
            String module = kind == null ? null : PublishedRequirements.counted(entry, at);
            String name = module == null ? null : PublishedRequirements.counted(entry, at);
            String form = name == null ? null : PublishedRequirements.counted(entry, at);
            String content = form == null ? null : PublishedRequirements.counted(entry, at);
            CopyTarget target = content == null ? null
                    : CopyTarget.readingWritten(kind, module, name);
            CopyRecord.Form readForm = target == null ? null : CopyRecord.Form.readingWritten(form);
            if (readForm == null || at[0] != entry.length()
                    || out.put(target, new CopyRecord(readForm, content)) != null) {
                return null;
            }
        }
        return out;
    }
}
