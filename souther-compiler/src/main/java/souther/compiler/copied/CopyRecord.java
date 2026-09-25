package souther.compiler.copied;

/**
 * What a declaration offers a reader to copy, as an artifact records it: which form the copy takes,
 * and what it says in that form.
 *
 * <p>Two of these are the same copy exactly when they are equal. The content is written so that two
 * compiles of one declaration write the same thing ({@link CopiedIdentity}), so comparing it is
 * comparing what a reader's classes were built from and not how its source was laid out.
 *
 * @param form    how the declaration is copied
 * @param content what it is copied as, in that form
 */
public record CopyRecord(Form form, String content) {

    public CopyRecord {
        if (form == null || content == null) {
            throw new IllegalArgumentException("a copy has a form and a content: " + form);
        }
    }

    /**
     * How a declaration is copied. A helper is copied as its closed definition, a value as its
     * constant where it folds to one and as its closed body where it does not, and a type's invariant
     * as its clauses.
     */
    public enum Form {
        CLOSED_HELPER("closed helper"),
        CONSTANT("constant"),
        CLOSED_BODY("closed body"),
        CLAUSES("clauses");

        private final String written;

        Form(String written) {
            this.written = written;
        }

        /** The words an artifact writes for it and a report shows. */
        public String written() {
            return written;
        }

        /** The form an artifact wrote as {@code written}, or null where it is no form this writes. */
        public static Form readingWritten(String written) {
            for (Form form : values()) {
                if (form.written.equals(written)) {
                    return form;
                }
            }
            return null;
        }
    }
}
