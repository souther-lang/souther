package souther.compiler.diag;

/**
 * Where something is, said so that it survives being collected with things from other files.
 *
 * <p>A {@link SourcePos} is a line and a column, which is enough while one file is being read and not
 * enough afterwards: a module's {@code example} rows are written in the module's own source and in any
 * number of attached {@code examples for} files, and once those rows are gathered under one name a
 * position on its own no longer says which file it came from.
 */
public record SourceRef(String sourceId, SourcePos pos) {

    public static SourceRef of(String sourceId, SourcePos pos) {
        return new SourceRef(sourceId, pos);
    }

    @Override
    public String toString() {
        return sourceId == null ? String.valueOf(pos) : sourceId + " " + pos;
    }
}
