package souther.compiler.meaning;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Whether a proposition holds, or fails, whichever way each of its parts that is no conjunction or
 * disjunction comes out.
 *
 * <p>Each such part is taken as free of every other: two parts are one only where one is the
 * other's denial and holds wherever the other fails, which is what {@code c || !c} needs. A
 * statement on the applications of a closure and its denial may both hold, and are two parts. So
 * an answer of yes is an answer about the
 * proposition, and an answer of no says only that this did not find one — two comparisons of one
 * number that cannot both fail are two free parts here, and their disjunction is not found to hold.
 *
 * <p>Up to {@link #PARTS_TRIED} parts. Beyond that every assignment is more than a reading asks to be
 * worked through, and the answer is no.
 */
public final class TruthTable {

    /** How many free parts a proposition is worked through for, at most. */
    static final int PARTS_TRIED = 10;

    private TruthTable() {}

    /** Whether {@code stated} holds whichever way its parts come out. */
    public static boolean holdsWhateverItsPartsAre(Proposition stated) {
        return everyAssignmentAnswers(stated, true);
    }

    /** Whether {@code stated} fails whichever way its parts come out. */
    public static boolean failsWhateverItsPartsAre(Proposition stated) {
        return everyAssignmentAnswers(stated, false);
    }

    private static boolean everyAssignmentAnswers(Proposition stated, boolean answer) {
        Map<String, Integer> parts = new LinkedHashMap<>();
        if (!partsOf(stated, parts) || parts.size() > PARTS_TRIED) {
            return false;
        }
        for (long assignment = 0; assignment < 1L << parts.size(); assignment++) {
            if (valueOf(stated, parts, assignment) != answer) {
                return false;
            }
        }
        return true;
    }

    /**
     * Gathers the free parts of {@code stated} into {@code into}, each under the spelling of the one
     * of it and its denial that spells first — or answers false where a part is one nothing read,
     * which comes out no way this can name.
     */
    private static boolean partsOf(Proposition stated, Map<String, Integer> into) {
        return switch (stated) {
            case Proposition.Always _ -> true;
            case Proposition.Unread _ -> false;
            case Proposition.All all -> all.parts().stream().allMatch(part -> partsOf(part, into));
            case Proposition.Any any -> any.parts().stream().allMatch(part -> partsOf(part, into));
            case Proposition.WhereItAnswers where ->
                    partsOf(where.answers(), into) && partsOf(where.states(), into);
            // A count of statements is one part: what holds whichever way it comes out holds
            // whichever way its statements do.
            case Proposition.Compared _, Proposition.Truth _, Proposition.InCases _,
                 Proposition.Present _, Proposition.SameValue _, Proposition.LastToHold _,
                 Proposition.Some _, Proposition.Carried _, Proposition.SomeReachable _,
                 Proposition.OnAnApplication _, Proposition.SoManyHold _ -> {
                into.putIfAbsent(spelledAs(stated), into.size());
                yield true;
            }
        };
    }

    private static boolean valueOf(Proposition stated, Map<String, Integer> parts,
                                   long assignment) {
        return switch (stated) {
            case Proposition.Always(boolean holds) -> holds;
            case Proposition.All all -> all.parts().stream()
                    .allMatch(part -> valueOf(part, parts, assignment));
            case Proposition.Any any -> any.parts().stream()
                    .anyMatch(part -> valueOf(part, parts, assignment));
            // Holds where it answers and states what it does; its denial is the same answering
            // with the statement denied, and comes out that way here as any other part does.
            case Proposition.WhereItAnswers where -> valueOf(where.answers(), parts, assignment)
                    && valueOf(where.states(), parts, assignment);
            case Proposition.Compared _, Proposition.Truth _, Proposition.InCases _,
                 Proposition.Present _, Proposition.SameValue _, Proposition.LastToHold _,
                 Proposition.Some _, Proposition.Carried _, Proposition.SomeReachable _,
                 Proposition.Unread _, Proposition.OnAnApplication _, Proposition.SoManyHold _ -> {
                String spelled = spelledAs(stated);
                boolean set = (assignment >> parts.get(spelled) & 1L) == 1L;
                yield spelled.equals(stated.key()) == set;
            }
        };
    }

    /**
     * The free part {@code part} comes out as: the spelling of whichever of it and its denial
     * spells first, where its denial holds wherever it fails ({@link
     * Proposition#deniedWhereverItFails}), so the two are one part; and its own spelling where not,
     * so it and its denial are two parts, free of each other.
     */
    private static String spelledAs(Proposition part) {
        if (!Proposition.deniedWhereverItFails(part)) {
            return part.key();
        }
        String denied = part.denied().key();
        return part.key().compareTo(denied) <= 0 ? part.key() : denied;
    }
}
