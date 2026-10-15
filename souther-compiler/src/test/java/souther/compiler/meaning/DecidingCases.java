package souther.compiler.meaning;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/** The cases a case of where a line decides stands for, written out, for a test to compare. */
public final class DecidingCases {

    private DecidingCases() {
    }

    /**
     * Each case {@code cases} stands for, as the conjunction of what it chose, each once and in the
     * order they are chosen.
     *
     * @throws IllegalArgumentException where they were more than were taken apart, which is no
     *                                  list of cases
     */
    public static List<Proposition> eachOf(DecidingCase.Cases cases) {
        Set<Proposition> out = new LinkedHashSet<>();
        chosen(List.of(), List.of(cases), out);
        return List.copyOf(out);
    }

    private static void chosen(List<Proposition> chosen, List<DecidingCase.Cases> toChoose,
                               Set<Proposition> into) {
        if (toChoose.isEmpty()) {
            into.add(Proposition.all(chosen));
            return;
        }
        List<DecidingCase.Cases> rest = toChoose.subList(1, toChoose.size());
        switch (toChoose.getFirst()) {
            case DecidingCase.Cases.One(var condition) -> {
                List<Proposition> more = new ArrayList<>(chosen);
                more.add(condition);
                chosen(more, rest, into);
            }
            case DecidingCase.Cases.EachOf(var alternatives) -> alternatives.forEach(one -> {
                List<DecidingCase.Cases> next = new ArrayList<>();
                next.add(one);
                next.addAll(rest);
                chosen(chosen, next, into);
            });
            case DecidingCase.Cases.Together(var factors) -> {
                List<DecidingCase.Cases> next = new ArrayList<>(factors);
                next.addAll(rest);
                chosen(chosen, next, into);
            }
            case DecidingCase.Cases.MoreThanWereTakenApart _ -> throw new IllegalArgumentException(
                    "cases more than were taken apart are not written out");
        }
    }
}
