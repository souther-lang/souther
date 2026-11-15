package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Weakening;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a combination is comes from the decisions of the model, and where a search looks for a row
 * comes from the classes of the input. A decision no one class of one axis states is still a
 * decision: its combinations stay owed, and the measure says what it could not tell about them.
 */
class AGroupTheClassesCannotPlaceIsStillOwedTest {

    @Test
    void aFieldBothCasesSpreadIsPlacedUnderEachCase() {
        AdequacyReport.BehaviorReport behavior = behaviorOf("""
                module m1

                data Src = Web | Phone | Ref
                data Common = { src: Src, n: Int }
                data A = { ...Common }
                data B = { ...Common, touches: Int }
                data L = A | B

                let band (s: Src): Int =
                    match s with
                        | Web   -> 10
                        | Phone -> 20
                        | Ref   -> 30

                let touchesOf (l: L): Int =
                    match l with
                        | A -> 0
                        | B { touches } -> touches

                behavior score : (l: L) -> Int
                let score (l) = band(l.src) + touchesOf(l)

                example score
                    | "a web" : (A { src = Web, n = 1 }) -> 10
                    | "a phone" : (A { src = Phone, n = 1 }) -> 20
                    | "b ref" : (B { src = Ref, n = 1, touches = 2 }) -> 32
                """);

        assertWhole(behavior);
    }

    @Test
    void theElseOfAConjunctionIsPlacedAsTheUnionOfWhatItLeaves() {
        AdequacyReport.BehaviorReport behavior = behaviorOf("""
                module m5

                data Reason = Young | Poor
                data Blocked = { reasons: List<Reason> }
                    invariant List.length(reasons) >= 1
                data Ok = { age: Int }

                behavior judge : (age: Int, income: Int, flag: Bool) -> Blocked | Ok
                    constructs Blocked, Ok

                let judge (age, income, flag) =
                    if Blocked { reasons = (if flag && age < 16 then [ Young ] else []) ++ [ Poor | income < 100 ] } as blocked
                    then blocked
                    else Ok { age = age }

                example judge
                    | "young and poor" : (10, 50, true) -> Blocked { reasons = [ Young, Poor ] }
                    | "young" : (10, 500, true) -> Blocked { reasons = [ Young ] }
                    | "poor" : (20, 50, true) -> Blocked { reasons = [ Poor ] }
                    | "ok" : (20, 500, true) -> Ok { age = 20 }
                    | "noflag" : (10, 500, false) -> Ok { age = 10 }
                """);

        assertWhole(behavior);
    }

    @Test
    void aGuardOnHowManyElementsAFilterKeptIsPlacedAsTheUnionOfTheKeepingWays() {
        AdequacyReport.BehaviorReport behavior = behaviorOf("""
                module m12

                data W = { a: Int, b: Int }

                behavior avg : (w: W) -> Int
                let avg (w) = {
                    let ok = List.filter(d -> d >= 17, [ w.a, w.b ])
                    guard List.length(ok) >= 1 else 0
                    List.sum(ok)
                }

                example avg
                    | "both" : (W { a = 20, b = 20 }) -> 40
                    | "a" : (W { a = 20, b = 1 }) -> 20
                    | "b" : (W { a = 1, b = 20 }) -> 20
                    | "none" : (W { a = 1, b = 1 }) -> 0
                """);

        // The else is what an empty sum is, so replacing it by the other arm changes no answer: an
        // equivalent rewrite, which is another measure's and not this one's.
        assertTrue(behavior.evidence().interaction().counted() > 0,
                "the combinations of the decisions are counted and not dropped");
        assertFalse(behavior.weakenedBy().causes().stream().anyMatch(
                        each -> each instanceof Weakening.MeetingsExistenceUndetermined
                                || each instanceof Weakening.MeetingsNotJoined
                                || each instanceof Weakening.MeetingsNotWalked),
                () -> "and the meeting is placed and joined: " + behavior.weakenedBy());
    }

    @Test
    void theSameGuardWithAnElseThatIsNotWhatAnEmptySumIsIsWhole() {
        AdequacyReport.BehaviorReport behavior = behaviorOf("""
                module m12b

                data W = { a: Int, b: Int }

                behavior avg : (w: W) -> Int
                let avg (w) = {
                    let ok = List.filter(d -> d >= 17, [ w.a, w.b ])
                    guard List.length(ok) >= 1 else 0 - 1
                    List.sum(ok)
                }

                example avg
                    | "both" : (W { a = 20, b = 20 }) -> 40
                    | "a" : (W { a = 20, b = 1 }) -> 20
                    | "b" : (W { a = 1, b = 20 }) -> 20
                    | "none" : (W { a = 1, b = 1 }) -> -1
                """);

        assertWhole(behavior);
    }

    @Test
    void aRelationBetweenTwoPositionsIsADecisionTheRowsAreHeldToWithoutAClassForIt() {
        AdequacyReport.BehaviorReport behavior = behaviorOf("""
                module m11

                data Reason = Same | Small
                data Blocked = { reasons: List<Reason> }
                    invariant List.length(reasons) >= 1
                data Ok = { x: Int }

                behavior judge : (x: Int, y: Int, z: Int) -> Blocked | Ok
                    constructs Blocked, Ok

                let judge (x, y, z) =
                    if Blocked { reasons = [ Same | x == y ] ++ [ Small | z < 3 ] } as blocked
                    then blocked
                    else Ok { x = x }

                example judge
                    | "both" : (1, 1, 1) -> Blocked { reasons = [ Same, Small ] }
                    | "same" : (1, 1, 5) -> Blocked { reasons = [ Same ] }
                    | "small" : (1, 2, 1) -> Blocked { reasons = [ Small ] }
                    | "ok" : (1, 2, 5) -> Ok { x = 1 }
                """);

        assertWhole(behavior);
    }

    private static void assertWhole(AdequacyReport.BehaviorReport behavior) {
        assertTrue(behavior.evidence().interaction().counted() > 0,
                "the combinations of the decisions are counted and not dropped");
        assertEquals(MeasurementStatus.COMPLETE, behavior.status(),
                () -> "and nothing is left unmeasured: " + behavior.weakenedBy());
    }

    private static AdequacyReport.BehaviorReport behaviorOf(String model) {
        Compilation compilation = ACompiledModel.measured(model, Adequacy.Asked.fullReport());
        return AdequacyReport.of(compilation).modules().getFirst().behaviors().getFirst();
    }
}
