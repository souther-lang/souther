package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Weakening;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * How many worlds a list of clues leaves is a statement about the clues: none, one, or more. A world
 * is kept by what a quantifier states of the input list, and also by a test the body made it with
 * that reads nothing of the input. That second one is the same on every run, so it is no decision
 * and the count is read as the statement it is.
 */
class ACountKeptByAQuantifierOverAnInputListIsOneStatementTest {

    private static final String MINI_WHODUNIT = """
            module example.mini

            import List ( flatMap, map, filter, all, any, allDistinctBy, length, get )

            data Suspect = Alice | Bob
            data Room    = Kitchen | Study
            data Placement = { who: Suspect, room: Room }
            data World = { culprit: Suspect, places: List<Placement> }

            data CulpritWasIn = { room: Room }
            data SawIn        = { who: Suspect, room: Room }
            data Innocent     = { who: Suspect }
            data Clue = CulpritWasIn | SawIn | Innocent

            let rooms    = [ Kitchen, Study ]
            let suspects = [ Alice, Bob ]

            let seatings =
                flatMap(a ->
                    map(b -> [ Placement { who = Alice, room = a }
                             , Placement { who = Bob,   room = b } ],
                        rooms),
                    rooms)
                    |> filter(seating -> allDistinctBy(p -> p.room, seating))

            let worlds =
                flatMap(culprit -> map(seating -> World { culprit = culprit, places = seating }, seatings),
                          suspects)

            let stood (places: List<Placement>, who: Suspect, room: Room): Bool =
                any(p -> p.who == who && p.room == room, places)

            let holds (clue: Clue, w: World): Bool =
                match clue with
                    | CulpritWasIn { room } -> stood(w.places, w.culprit, room)
                    | SawIn { who, room }   -> stood(w.places, who, room)
                    | Innocent { who }      -> w.culprit /= who

            data Unraveled = { culprit: Suspect }
            data NoConsistentStory
            data StillAmbiguous

            behavior solve : (clues: List<Clue>) -> Unraveled | NoConsistentStory | StillAmbiguous
                constructs Unraveled

            let solve (clues) = {
                let fitting = filter(w -> all(clue -> holds(clue, w), clues), worlds)
                match get(0, fitting) with
                    | None   -> NoConsistentStory
                    | Some w ->
                        if length(fitting) == 1
                        then Unraveled { culprit = w.culprit }
                        else StillAmbiguous
            }

            example solve
                | "one" : ([ CulpritWasIn { room = Kitchen }, SawIn { who = Alice, room = Study } ])
                    -> Unraveled { culprit = Bob }
                | "none" : ([ Innocent { who = Alice }, Innocent { who = Bob } ]) -> NoConsistentStory
                | "several" : ([ ]) -> StillAmbiguous
            """;

    @Test
    void theNumberOfWorldsAListOfCluesLeavesIsNoMeetingOfTheirKeeping() {
        AdequacyReport.BehaviorReport behavior = behaviorOf(MINI_WHODUNIT);

        assertFalse(behavior.weakenedBy().causes().stream()
                        .anyMatch(Weakening.MeetingsNotJoined.class::isInstance),
                () -> "the count is read as the statement it is: " + behavior.weakenedBy());
        assertEquals(MeasurementStatus.COMPLETE, behavior.status(),
                () -> "and nothing is left unmeasured: " + behavior.weakenedBy());
    }

    private static AdequacyReport.BehaviorReport behaviorOf(String model) {
        Compilation compilation = ACompiledModel.measured(model, Adequacy.Asked.fullReport());
        return AdequacyReport.of(compilation).modules().getFirst().behaviors().getFirst();
    }
}
