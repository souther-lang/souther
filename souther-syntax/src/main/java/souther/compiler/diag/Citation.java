package souther.compiler.diag;

import java.util.LinkedHashMap;
import java.util.SequencedMap;

/**
 * Where the code something is about is written, as a report is entitled to say it.
 *
 * <p>A coordinate is put to two uses and only one of them can be wrong. Sending a reader somewhere —
 * a caret, a range, an editor jumping — is right whatever the coordinate stands for, because it is
 * where this compile met the code and the only place a reader can be sent. Saying the code is
 * <em>written</em> there is right only where it is. Nothing distinguished the two, so every surface
 * that wanted the first published the second: an unreached arm of {@code List.filter} was reported
 * at the caller's {@code 15:23} by the adequacy report in both of its renderings and by the JSON a
 * diagnostic is read from, and one renderer out of four said what the coordinate stood for.
 *
 * <p>So the two are separate values. {@link SourcePos} is where this compile placed a node, and every
 * pass reads it freely. This is the other one, and it is what a report holds: a {@link Site}, a
 * finding, a reason carries this rather than a coordinate, so a surface written later is handed the
 * answer rather than the raw place.
 *
 * <p>No accessor spans the two cases. A reader that wants the coordinate — to put a caret at it —
 * says which case it is in first, and having said so has seen that the other exists. An
 * {@code at()} on this interface would be the shortest way back to the defect: every caller would
 * write it, the sum would decorate nothing, and the second case would go unread again.
 *
 * <p>Built one way. {@link #of} asks the coordinate's provenance to project itself, which is the only
 * thing {@link WrittenAt} will do and is package-private so that it stays so. There is no
 * constructor a caller could reach to state a place the compiler did not observe.
 */
public sealed interface Citation permits Citation.Written, Citation.OutOfSight {

    /** The code is written at {@link #at()}, which is therefore both where to send a reader and
     *  where the code is. */
    sealed interface Written extends Citation permits WrittenCitation {
        SourceRef at();
    }

    /**
     * The code is written in {@link #declaration()}, which this compile has no source for.
     * {@link #reachedFrom()} is where this compile met it — where to send a reader, and not where the
     * code is.
     */
    sealed interface OutOfSight extends Citation permits OutOfSightCitation {
        /** The name a reader here reaches that code by: {@code List.filter}. */
        String declaration();

        /** The call the body was spliced into. A place in a file the reader holds. */
        SourceRef reachedFrom();
    }

    /** What a report may say about where {@code ref} names code written. */
    static Citation of(SourceRef ref) {
        return ref.pos().writtenAt().cite(ref);
    }

    /** The same, for a coordinate that carries the source it is in — which is every coordinate a
     *  diagnostic is built at, the source having been part of the position since positions were
     *  gathered across files. */
    static Citation of(SourcePos pos) {
        return of(new SourceRef(pos.sourceId(), pos));
    }

    /**
     * What a document writes about this, as the fields it writes them under.
     *
     * <p>One writer for two documents. The adequacy report and the JSON a diagnostic is read from
     * both say this, and a consumer reading one of them should not have to learn a second vocabulary
     * to read the other — which is what would have happened, the two being rendered in different
     * modules by different machinery.
     *
     * <p>Written on both arms, {@code here} included. The field is added to a schema that already has
     * documents without it, so its absence has to go on meaning "this document does not say" — and an
     * emitter that wrote it only where the answer was interesting would put "the code is here" and
     * "written before anyone asked" under one silence.
     */
    default SequencedMap<String, String> writtenAtFields() {
        SequencedMap<String, String> fields = new LinkedHashMap<>();
        switch (this) {
            case Written _ -> fields.put("kind", "here");
            case OutOfSight out -> {
                fields.put("kind", "outOfSight");
                fields.put("declaration", out.declaration());
            }
        }
        return fields;
    }

    /**
     * This as a line of a report about {@code sectionSource}, with the sources under the names
     * {@code names} gives them.
     *
     * <p>A line and a column are a place only beside a file. They are written on their own where the
     * section already names the file, and with the file where it does not — a coordinate from another
     * source, printed bare, points at whatever happens to sit at those numbers in the one the reader
     * has in mind.
     */
    default String said(SourceNameResolver names, String sectionSource) {
        return switch (this) {
            case Written written -> place(written.at(), names, sectionSource);
            case OutOfSight out -> "`" + out.declaration() + "`, reached at "
                    + place(out.reachedFrom(), names, sectionSource);
        };
    }

    /** Never handed a null: both arms require the place they are about. The tolerance the report's
     *  own writer used to have is gone rather than carried over, and a fallback standing in for it
     *  would read as a case somebody had thought about. */
    private static String place(SourceRef ref, SourceNameResolver names, String sectionSource) {
        if (ref.sourceId() == null || ref.sourceId().equals(sectionSource)) {
            return String.valueOf(ref.pos());
        }
        return names.nameOf(ref.sourceId()) + ":" + ref.pos();
    }
}
