package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A walk over a list that holds one element or none on every run owes neither rewrite, wherever
 * the list comes from: no row can tell the walk from the walk stopped after its first element, or
 * from every step handed the seed, since there is no second step to stop before or to hand it to.
 *
 * <p>A list written out where it is walked was read that way already. The same list answered by a
 * helper, by the arms of a {@code match} or by a comprehension with a guard alone is the same walk,
 * and was left open for want of a row nobody can write.
 */
class AWalkOverAListOfAtMostOneElementOwesNoRewriteTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    @Test
    void aListWrittenOutIsWalkedNoFurtherThanItsFirst() {
        assertOwesNoWalkRewrite(measured("""
                module repro.written

                behavior bump : (n: Int) -> List<Int>
                let bump (n) = List.map(x -> x + 1, [ n ])

                example bump
                    | "one" : (3) -> [ 4 ]
                """));
    }

    @Test
    void aListAHelperAnswersIsRead() {
        assertOwesNoWalkRewrite(measured("""
                module repro.helper

                let wrap (n: Int): List<Int> = [ n ]

                behavior bump : (n: Int) -> List<Int>
                let bump (n) = List.map(x -> x + 1, wrap(n))

                example bump
                    | "one" : (3) -> [ 4 ]
                """));
    }

    @Test
    void aListEveryArmOfAMatchAnswersIsRead() {
        assertOwesNoWalkRewrite(measured("""
                module repro.arms

                data Kind = Tagged | Plain

                data Item = { kind: Kind, n: Int }

                let tagOf (i: Item): List<Int> =
                    match i.kind with
                        | Tagged -> [ i.n ]
                        | Plain  -> []

                behavior tags : (i: Item) -> List<Int>
                let tags (i) = List.map(x -> x + 1, tagOf(i))

                example tags
                    | "tagged" : (Item { kind = Tagged, n = 3 }) -> [ 4 ]
                    | "plain" : (Item { kind = Plain, n = 3 }) -> [ ]
                """));
    }

    @Test
    void aComprehensionWithAGuardAloneIsRead() {
        assertOwesNoWalkRewrite(measured("""
                module repro.comprehension

                behavior bump : (n: Int) -> List<Int>
                let bump (n) = List.map(x -> x + 1, [ n | n > 0 ])

                example bump
                    | "positive" : (3) -> [ 4 ]
                    | "zero" : (0) -> [ ]
                """));
    }

    /** One arm of the match answers two, so a row can walk a second step and the rewrites are owed. */
    @Test
    void aListOneArmOfWhichHoldsTwoIsStillOwedBothRewrites() {
        Compilation compilation = measured("""
                module repro.two

                data Kind = Tagged | Plain

                data Item = { kind: Kind, n: Int }

                let tagOf (i: Item): List<Int> =
                    match i.kind with
                        | Tagged -> [ i.n, i.n ]
                        | Plain  -> []

                behavior tags : (i: Item) -> List<Int>
                let tags (i) = List.map(x -> x + 1, tagOf(i))

                example tags
                    | "tagged" : (Item { kind = Tagged, n = 3 }) -> [ 4, 4 ]
                    | "plain" : (Item { kind = Plain, n = 3 }) -> [ ]
                """);

        assertEquals(List.of("fold_after_one_step", "fold_from_the_seed"),
                walkRewritesOwedOfMap(compilation), () -> page(compilation));
    }

    /** No rewrite of the walk is owed, and so none is left open either. */
    private static void assertOwesNoWalkRewrite(Compilation compilation) {
        assertEquals(List.of(), walkRewritesOwedOfMap(compilation), () -> page(compilation));
        assertEquals(List.of(), undecided(compilation), () -> page(compilation));
    }

    /**
     * What is owed is the obligation list and not the page: a rewrite no row can be asked about is
     * left out of it, and one the page does not word as open is still owed.
     */
    private static List<String> walkRewritesOwedOfMap(Compilation compilation) {
        JsonNode replacement = JSON.readTree(AdequacyReport.of(compilation)
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .get("modules").get(0).get("behaviors").get(0).get("replacement");
        List<String> owed = new ArrayList<>();
        for (JsonNode each : replacement.get("obligations")) {
            JsonNode id = each.get("obligationId");
            if (id.has("definition") && id.get("definition").asString().equals("map")
                    && id.get("rewrite").asString().startsWith("fold_")) {
                owed.add(id.get("rewrite").asString());
            }
        }
        return owed;
    }

    private static List<String> undecided(Compilation compilation) {
        return page(compilation).lines().map(String::strip)
                .filter(line -> line.startsWith("? not decided whether a row would come out"))
                .toList();
    }

    private static String page(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        return ACompiledModel.compiles(compilation);
    }
}
