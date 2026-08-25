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
    record Built(RowId row) implements ClassDisposition {

        public Built {
            if (row == null) {
                throw new IllegalArgumentException("a class a row was composed for names the row");
            }
        }
    }

    /**
     * No row came of it, and why.
     *
     * <p>Which of the two kinds of news that is belongs to the reason and not to this. A strategy
     * took the class and composed nothing: sometimes because the rules leave no value there, which
     * a reader may act on, and sometimes because this compiler fell short, which they may not.
     * Said here as though it were always the second, a reason that settles the question would be
     * printed under a sentence denying it.
     */
    record Unresolved(Generator.UnresolvedCombination why) implements ClassDisposition {

        public Unresolved {
            if (why == null) {
                throw new IllegalArgumentException("a class nothing came of says what happened");
            }
        }
    }
}
