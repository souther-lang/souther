package souther.compiler.diag;

import souther.compiler.source.SourceId;

import java.util.Objects;
import java.util.Optional;

/**
 * What the surface showing a report answers for it: which file it is listing the report under, and
 * which text it is reading.
 *
 * <p>Two questions, and they were one field. {@code Located} carried a source that meant "the source
 * the primary region is in" where the region already said so, and meant "the file to list this under"
 * where the report pointed at nothing — so a report whose region named its file arrived with the
 * field empty and nothing was lost, while a report that pointed nowhere arrived with it set and it
 * was the only answer there was. Measured over this suite, the first was 117 of 266 primaries
 * reaching a renderer and the second was all 10 reports that pointed at nothing.
 *
 * <p>Neither is read off the other. A file a report is listed under is a decision about where an
 * author will look for it, and the text a surface is reading is a fact about what that surface
 * holds; an editor publishing one document's markers is reading that document while listing a report
 * whose code is in another file.
 *
 * <p>Both optional, and their absence means different things. Nothing to list it under is a caller
 * that has no files — a renderer handed one diagnostic and asked what it says. Nothing being read is
 * a caller that did not say, and a report in a text nobody named then has no place to offer
 * ({@link SpotResolution.TextWasNotProvided}) rather than a place shown against a text somebody
 * guessed at.
 */
public record ReportContext(Optional<SourceId> filedUnder, Optional<TextBeingRead> textBeingRead) {

    public ReportContext {
        Objects.requireNonNull(filedUnder, "say which file this is listed under, or say none");
        Objects.requireNonNull(textBeingRead, "say which text is being read, or say none");
    }

    /** A caller with no files: nothing to list a report under and no text to quote. */
    public static final ReportContext NONE =
            new ReportContext(Optional.empty(), Optional.empty());

    /** A compile showing a report on one of its own sources, which is both where the report is
     *  listed and the text being read. */
    public static ReportContext inFile(SourceId source) {
        return source == null ? NONE
                : new ReportContext(Optional.of(source),
                        Optional.of(new TextBeingRead.UnderAnId(source)));
    }

    /**
     * A surface listing a report under one file while reading another — an editor putting a marker
     * on the document it is publishing for a report whose primary is in a different source.
     */
    public static ReportContext of(SourceId filedUnder, SourceId textBeingRead) {
        return new ReportContext(Optional.ofNullable(filedUnder),
                Optional.ofNullable(textBeingRead).map(TextBeingRead.UnderAnId::new));
    }

    /** A caller holding a text it has no identity for, and quoting the report from it — or holding
     *  none, which is {@link #NONE} and not a text that happens to be empty. */
    public static ReportContext ofTheTextItself(SourceContext text) {
        return text == null ? NONE
                : new ReportContext(Optional.empty(),
                        Optional.of(new TextBeingRead.AsHandedOver(text)));
    }
}
