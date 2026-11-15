package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A fold's step may stop a run on what it reads, and what a later comparison reads is none of
 * that. A name the step binds, by a {@code let} or by an inlined library call, stands for what it
 * was bound to, so binding one leaves the places the step may stop on as they are written without
 * it.
 *
 * <p>Each spelling that binds is measured against the spelling that writes the expression where
 * it is used: both are asked for what the membership after the fold was not read at, and what they
 * agree on must not be empty by both falling silent, so the spelling without a name is held to
 * read the membership too.
 */
class ANameBoundInsideAFoldStepDoesNotMakeALaterComparisonUnreachedTest {

    private static final String MODEL = """
            module example.fold

            behavior piped : (m: Map<String, Int>, prices: Map<String, Int>, s: String, prev: List<String>) -> Bool
            let piped (m, prices, s, prev) = {
                let total = Map.fold((acc, k, q) -> { let p = Map.get(k, prices) |> Option.withDefault(0)
                    acc + p + q }, 0, m)
                List.contains(s, prev)
            }
            example piped
                | "no" : ([ ("a", 2) ], [ ("a", 3) ], "a", [ "b" ]) -> false
                | "yes" : ([ ("a", 2) ], [ ("a", 3) ], "a", [ "a" ]) -> true

            behavior called : (m: Map<String, Int>, prices: Map<String, Int>, s: String, prev: List<String>) -> Bool
            let called (m, prices, s, prev) = {
                let total = Map.fold((acc, k, q) -> { let p = Option.withDefault(0, Map.get(k, prices))
                    acc + p + q }, 0, m)
                List.contains(s, prev)
            }
            example called
                | "no" : ([ ("a", 2) ], [ ("a", 3) ], "a", [ "b" ]) -> false
                | "yes" : ([ ("a", 2) ], [ ("a", 3) ], "a", [ "a" ]) -> true

            let line (k: String, q: Int, prices: Map<String, Int>) = {
                let p = Map.get(k, prices) |> Option.withDefault(0)
                p + q
            }

            behavior helper : (m: Map<String, Int>, prices: Map<String, Int>, s: String, prev: List<String>) -> Bool
            let helper (m, prices, s, prev) = {
                let total = Map.fold((acc, k, q) -> acc + line(k, q, prices), 0, m)
                List.contains(s, prev)
            }
            example helper
                | "no" : ([ ("a", 2) ], [ ("a", 3) ], "a", [ "b" ]) -> false
                | "yes" : ([ ("a", 2) ], [ ("a", 3) ], "a", [ "a" ]) -> true

            behavior unnamed : (m: Map<String, Int>, prices: Map<String, Int>, s: String, prev: List<String>) -> Bool
            let unnamed (m, prices, s, prev) = {
                let total = Map.fold((acc, k, q) -> acc + (Map.get(k, prices) |> Option.withDefault(0)) + q, 0, m)
                List.contains(s, prev)
            }
            example unnamed
                | "no" : ([ ("a", 2) ], [ ("a", 3) ], "a", [ "b" ]) -> false
                | "yes" : ([ ("a", 2) ], [ ("a", 3) ], "a", [ "a" ]) -> true
            """;

    private static Map<String, PartitionEvidence> measured() {
        Compilation compilation = ACompiledModel.measured(MODEL, Adequacy.Asked.fullReport());
        Map<String, PartitionEvidence> out =
                compilation.db().ask(new Adequacy.Coverage("example.fold")).value();
        assertNotNull(out, "the model under test compiles");
        return out;
    }

    /** Every place left unread and why. */
    private static List<String> notRead(PartitionEvidence evidence) {
        return evidence.notRead().stream().map(left -> left.at() + " " + left.reason()).toList();
    }

    /** The places left unread for want of a showing that a run gets to the comparison. */
    private static List<String> notShownToGetTo(PartitionEvidence evidence) {
        return evidence.notRead().stream()
                .filter(left -> left.reason()
                        == UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE)
                .map(PartitionEvidence.NotRead::at)
                .toList();
    }

    @Test
    void aNameTheStepBindsLeavesTheMembershipAfterTheFoldReadAsTheSpellingWithoutOneDoes() {
        Map<String, PartitionEvidence> measured = measured();
        Map<String, List<String>> left = new LinkedHashMap<>();
        for (String name : List.of("piped", "called", "helper", "unnamed")) {
            assertNotNull(measured.get(name), name);
            left.put(name, notRead(measured.get(name)));
        }
        Map<String, List<String>> expected = new LinkedHashMap<>();
        for (String name : left.keySet()) {
            expected.put(name, left.get("unnamed"));
        }
        assertEquals(expected, left);
    }

    @Test
    void theSpellingWithoutANameReadsTheMembershipAtBothPlaces() {
        PartitionEvidence unnamed = measured().get("unnamed");
        assertNotNull(unnamed);
        assertEquals(List.of(), notShownToGetTo(unnamed));
    }
}
