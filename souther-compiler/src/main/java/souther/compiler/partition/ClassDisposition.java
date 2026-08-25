package souther.compiler.partition;

/**
 * What one run of the generator did about one class it was asked for.
 *
 * <p>Which class is the key it is filed under and is not repeated here. Carried inside as well, a
 * map could hold an entry filed under one class whose value named another, and the identity a
 * reader joined a finding by would be one of two answers.
 *
 * <p>Every class the plan names has one of these. A class with none used to mean the search never
 * reached it, and what a reader made of that absence was a guess — so the absence is gone and each
 * of the ways a run declines to look says so in its own entry.
 */
public sealed interface ClassDisposition {

    /** A row was composed for it, which is this row. */
    record Built(RowId row) implements ClassDisposition {}

    /** No row came of it, and why. Never a statement that none exists. */
    record Unresolved(Generator.UnresolvedCombination why) implements ClassDisposition {

        public Unresolved {
            if (why == null) {
                throw new IllegalArgumentException("a class nothing came of says what happened");
            }
        }
    }
}
