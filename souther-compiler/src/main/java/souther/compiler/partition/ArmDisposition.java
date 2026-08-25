package souther.compiler.partition;

import souther.compiler.reading.PathAccess;

import java.util.List;

/**
 * What one run of the generator did about one arm it was asked for.
 *
 * <p>Which arm is the key it is filed under, the same way a class's is.
 *
 * <p>Three answers because they are three pieces of news. A row was composed; a search ran at every
 * place a row could have come from and came back with what each of them said; or there was nowhere
 * to look at all, which the reading of the body settles and no search is involved in. Told as one,
 * a reader could not tell an arm the model refuses from one this compiler could not state a way
 * into.
 */
public sealed interface ArmDisposition {

    /** A row was composed for a combination that takes it, or along the way into it. */
    record Built(RowId row) implements ArmDisposition {}

    /**
     * No row came of the places a row could have come from, and what each of them came to.
     *
     * <p>All of them, because they are not one fact. One place stopping at the search's budget and
     * another the model's own rules refuse are different news — the first says a row may still be
     * writable and the second says the model settles it — and the arm is answered by the whole of
     * what was tried rather than by whichever was walked first.
     */
    record Unresolved(List<Generator.UnresolvedCombination> why) implements ArmDisposition {

        public Unresolved {
            why = List.copyOf(why);
            if (why.isEmpty()) {
                throw new IllegalArgumentException(
                        "an arm nothing was tried at is one with no way into it");
            }
        }
    }

    /**
     * Nothing was tried, because the reading of the body has no way into this arm to try.
     *
     * <p>Which is two pieces of news and the reading says which: no run reaches the arm at all, or
     * this compiler cannot state what steers a row there. Neither is a search that failed, and
     * carrying either as one would tell a reader a value was looked for.
     */
    record NoWayIn(PathAccess access) implements ArmDisposition {

        public NoWayIn {
            if (access instanceof PathAccess.Ways) {
                throw new IllegalArgumentException(
                        "an arm with ways into it is one this search had somewhere to look");
            }
        }
    }
}
