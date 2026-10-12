package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.ReachabilityGap;
import souther.compiler.types.WrittenOwner;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many candidates every clue lets stand, held against one, is looked for at every point of its
 * line — with clues of either kind in one list, and however many candidates there are.
 *
 * <p>{@code length(filter(w -> all(c -> holds(c, w), cs), suspects)) == 1} is decided by a clue
 * only where that clue alone rules a candidate in or out, and a row standing at a point of it has
 * to hold clues of both kinds: a {@code Clear} of one candidate beside a {@code Did} of another.
 * What it asks of the clues is one of as many things as there are candidates, each a statement
 * about every clue, so a row is composed against the statement whole rather than along each of
 * them — which is what leaves a point past more candidates than are looked along one at a time
 * still offered a row.
 */
class HowManyCandidatesFitIsComposedForWithCluesOfEachKindTest {

    /** Three candidates. */
    private static final String THREE = source(List.of("Ann", "Ben", "Cat"));

    /** One candidate more than are looked along one at a time. */
    private static final String PAST_THE_FIGURE = source(IntStream
            .rangeClosed(0, CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum())
            .mapToObj(each -> "W" + each).toList());

    private static String source(List<String> candidates) {
        String each = String.join(" | ", candidates);
        String all = String.join(", ", candidates);
        return """
                module probe.clues

                import List ( filter, all, get, length )

                data Who = CANDIDATES
                data Did = { who: Who }
                data Clear = { who: Who }
                data Clue = Did | Clear
                data One
                data NotOne
                data NoneFits

                let suspects = [ SUSPECTS ]

                let holds (c: Clue, w: Who): Bool =
                    match c with
                        | Did { who }   -> w == who
                        | Clear { who } -> w /= who

                behavior f : (cs: List<Clue>) -> One | NotOne | NoneFits

                let f (cs) = {
                    let fitting = filter(w -> all(c -> holds(c, w), cs), suspects)
                    match get(0, fitting) with
                        | None   -> NoneFits
                        | Some w -> if length(fitting) == 1 then One else NotOne
                }

                example f
                    | "one named" : ([ Did { who = FIRST } ]) -> One
                    | "none said" : ([]) -> NotOne
                """.replace("CANDIDATES", each).replace("SUSPECTS", all)
                .replace("FIRST", candidates.getFirst());
    }

    @Test
    void everyPointOfHowManyFitIsOfferedARow() {
        List<ItemAssessment.Owed> owed = searchedAt(owedAtHowManyFit(THREE));
        assertFalse(owed.isEmpty(), "the line of how many fit is owed rows");
        for (ItemAssessment.Owed item : owed) {
            assertTrue(item.searches().rowToOffer().isPresent(),
                    () -> "a row standing at the point is offered: " + item.searches());
        }
    }

    /**
     * Past more candidates than are looked along one at a time, every point is still offered a
     * row, and no search says it looked along the way whole without the statement.
     */
    @Test
    void pastTheFigureEveryPointIsStillOfferedARow() {
        List<ItemAssessment.Owed> owed = searchedAt(owedAtHowManyFit(PAST_THE_FIGURE));
        assertFalse(owed.isEmpty(), "the line of how many fit is owed rows");
        for (ItemAssessment.Owed item : owed) {
            assertTrue(item.searches().rowToOffer().isPresent(),
                    () -> "a row standing at the point is offered: " + item.searches());
            for (ItemAssessment.Attempt each : item.searches().each()) {
                if (each instanceof ItemAssessment.Attempt.Searched searched) {
                    assertTrue(searched.uncomposed().onTheWay().stream()
                                    .noneMatch(ReachabilityGap.LookedAlongWhole.class::isInstance),
                            () -> "composed against the statement whole: " + searched);
                }
            }
        }
    }

    /** Those of {@code owed} a row was looked for at: no row already written stands there. */
    private static List<ItemAssessment.Owed> searchedAt(List<ItemAssessment.Owed> owed) {
        return owed.stream().filter(ItemAssessment.Owed::worthSearching).toList();
    }

    /** What was owed at each point of the line `f` itself draws, which is how many fit. */
    private static List<ItemAssessment.Owed> owedAtHowManyFit(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        List<BorderAssessment> edges = compilation.db()
                .ask(new Adequacy.BoundarySearch("probe.clues", "f")).value();
        List<ItemAssessment.Owed> out = new ArrayList<>();
        for (BorderAssessment each : edges) {
            if (!each.border().origin().comparisonAt()
                    .map(at -> at.origin().owner() instanceof WrittenOwner.Body(var _, var in)
                            && in.equals("f"))
                    .orElse(false)) {
                continue;
            }
            for (ItemAssessment item : each.items().values()) {
                if (item instanceof ItemAssessment.Owed owed) {
                    out.add(owed);
                }
            }
        }
        return out;
    }
}
