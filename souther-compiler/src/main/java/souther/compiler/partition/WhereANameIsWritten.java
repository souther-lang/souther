package souther.compiler.partition;

import souther.compiler.inputs.NameReach;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Predicate;

/**
 * Every place a row that is already some cases may write the value a name names, and whether some
 * way of writing it reached a place nothing worked out.
 *
 * <p><b>The place a name is read is the place a row writes it, except at a name every case of a
 * sum spreads.</b> There the rules name the sum's own field and a row writes one of the cases, so
 * the value stands under whichever case the row turns out to be — and a row asked to write at the
 * sum's own name writes nowhere. One answer for every writer that has to put a value somewhere: a
 * number a cut asks for and a container a membership hands values to are written under the cases
 * the same way, and two walks of the crossings would part over the first case one of them read
 * differently.
 *
 * <p><b>Every case and not one of them,</b> in the order the model declares them, because which
 * case the row is decides which rules hold of the value and is the writer's to search. Only the
 * cases the row can be beside what it already is: a case the two do not hold together at is no way
 * of this row, and nothing below it is left open either.
 *
 * <p><b>A case whose reading stopped is no place to write and is not nothing either.</b> The cases
 * that did put the name somewhere are ways, and the ones whose reading stopped before putting it
 * anywhere are positions whose rules were never read — so a writer that found nothing under the
 * first may conclude nothing about the model, since the second may have what they lacked.
 * ({@link NameReach.Standing.CasesIncomplete} says the same of itself.) Only where the row can be
 * that case, as with every other: one the row is already kept out of leaves nothing open.
 *
 * @param places           where the row may write the value, each with what the row is taken to
 *                         be to write it there
 * @param someNotWorkedOut whether a way of this row reached a place whose holding nothing worked
 *                         out: a case whose reading stopped, or a place the writer's own reading
 *                         did not answer for
 */
record WhereANameIsWritten(List<Place> places, boolean someNotWorkedOut) {

    WhereANameIsWritten {
        places = List.copyOf(places);
    }

    /**
     * One place a row may write the value at.
     *
     * @param position where the value stands, under the cases taken to reach it
     * @param taken    what the row is taken to be to write it there: what it already was, and
     *                 every case on the way
     */
    record Place(TermPath position, Requirements taken) {}

    /**
     * Where a row that is already {@code trying} may write the value at {@code path}.
     *
     * @param answered whether the writer's reading answered for a place reached: the values a
     *                 number may take there were worked out, or the place is one a composer builds.
     *                 A place it did not answer for is not written at, and is said to be left open
     */
    static WhereANameIsWritten of(NameReach reach, TermPath path, Requirements trying,
                                  Predicate<TermPath> answered) {
        List<Place> to = new ArrayList<>();
        boolean notWorkedOut = followed(reach, path, trying, 0, answered, to);
        return new WhereANameIsWritten(to, notWorkedOut);
    }

    /**
     * The places from {@code here} on, added to {@code to}, and whether some way from here ended at
     * a place nothing worked out.
     *
     * <p>Followed one crossing at a time, since a name under two sums is moved by the outer one
     * before the inner one can see it ({@link NameReach#standingOf}); bounded by the crossings the
     * walk recorded, because each step takes one of them and no step takes one twice. Running past
     * that is this compiler disagreeing with its own reading rather than a search that could be
     * allowed more.
     */
    private static boolean followed(NameReach reach, TermPath here, Requirements trying,
                                    int crossed, Predicate<TermPath> answered, List<Place> to) {
        if (crossed > reach.crossings().size()) {
            throw new IllegalStateException(
                    "a name was followed past every crossing this reading recorded: " + here);
        }
        if (!(trying.merge(here.requirements())
                instanceof Requirements.Merge.Merged(Requirements taken))) {
            return false;
        }
        return switch (reach.standingOf(here)) {
            case NameReach.Standing.AtThePathItself _ -> {
                if (!answered.test(here)) {
                    yield true;
                }
                to.add(new Place(here, taken));
                yield false;
            }
            case NameReach.Standing.UnderTheCases(var standings) ->
                    under(reach, standings, taken, crossed, answered, to);
            // The cases that put the name somewhere are ways, and the ones whose reading stopped
            // leave the rest open — those of them the row can be. A case the row is already kept
            // out of is no way of it, read or not.
            case NameReach.Standing.CasesIncomplete(var standings, var stopped) ->
                    under(reach, standings, taken, crossed, answered, to)
                            | anyOfThem(stopped, taken);
        };
    }

    /** Whether the row, already {@code taken}, can be one of the cases whose reading stopped. */
    private static boolean anyOfThem(List<NameReach.NotStanding> stopped, Requirements taken) {
        for (NameReach.NotStanding each : stopped) {
            if (taken.merge(Requirements.NONE.and(each.at(), each.branch()))
                    instanceof Requirements.Merge.Merged) {
                return true;
            }
        }
        return false;
    }

    private static boolean under(NameReach reach, List<NameReach.CaseStanding> standings,
                                 Requirements taken, int crossed, Predicate<TermPath> answered,
                                 List<Place> to) {
        boolean notWorkedOut = false;
        for (NameReach.CaseStanding standing : standings) {
            notWorkedOut |= followed(reach, standing.position(), taken, crossed + 1, answered,
                    to);
        }
        return notWorkedOut;
    }
}
