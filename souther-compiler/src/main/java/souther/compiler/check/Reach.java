package souther.compiler.check;

import souther.compiler.types.ValueName;

/**
 * What a module's value namespace answers about a name written in it.
 *
 * <p>The counterpart of {@link souther.compiler.types.Denotation}, which says the same three things
 * about the type namespace, and written because the two were not the same three. A name an import
 * line was to bring in and could not stood for nothing as a type and was simply absent as a value,
 * so the author of one mistaken import line was told about it again at every use of the name —
 * once on the line, and once in each body where nothing is wrong.
 *
 * <p>The two namespaces are projections of one decision now, so the middle answer is the same
 * answer in both. What parts it from the third is whether anything has been said yet: a name that
 * stands for nothing was accounted for on the import line, and a name nothing here writes still
 * owes the reader a report.
 */
public sealed interface Reach {

    /** What writing the name reaches. */
    record Reaches(ValueName name) implements Reach {

        public Reaches {
            if (name == null) {
                throw new IllegalArgumentException("a name that reaches reaches something");
            }
        }
    }

    /**
     * In scope and reaching nothing: a name an import line that could not do its job stands in
     * for.
     *
     * <p>What is wrong was reported on that line, so a use of the name says nothing more — it is
     * read as a name nothing answered and the traversal goes on past it. This is the answer that is
     * already accounted for.
     */
    record StandsForNothing() implements Reach {}

    /**
     * Nothing here is written that way.
     *
     * <p>Nobody has said anything about it, so the reader of the position is the one to report it.
     * This is the answer that still owes a diagnostic.
     */
    record NotInScope() implements Reach {}

    Reach STANDS_FOR_NOTHING = new StandsForNothing();

    Reach NOT_IN_SCOPE = new NotInScope();
}
