package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.partition.ObligationIdentity;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Composition;
import souther.compiler.query.GenerationScope;
import souther.compiler.query.OfferingRequest;
import souther.compiler.query.Settlements;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the rows offered for a model settle does not turn on how the names of a union's cases
 * compare.
 *
 * <p>A union is its members: {@code A | B} and {@code B | A} are one type, and nothing below the
 * declaration can say which of them was written first. So two models differing only in the words
 * their cases are spelled with are one model as far as what a row is owed for goes, and the
 * obligations their offerings settle are the same obligations.
 *
 * <p><b>The two spellings are the same text.</b> The names are exchanged for names of the same
 * length, so every position in the two models is the same position and every obligation is the same
 * obligation. What the exchange moves is the order the names compare in, and nothing else.
 *
 * <p><b>What is compared is what the rows settle, not the block they are rendered into.</b> A row's
 * text says which case it was written with, and holding that steady would hold this compiler to
 * where it decides such a thing rather than to what the decision is about — the case a row stands a
 * dependency in with is free to move, and what the offering covers is not.
 *
 * <p>The model is written so that something depends on the answer. A truth read off a place inside
 * an answer is a condition no demand states, so nothing composes a row to go through the arms below
 * it; whether they are covered at all is whatever the rows composed for the input's own points turn
 * out to do. That is where an arbitrary case is visible as coverage rather than as a word.
 */
class WhatTheOfferedRowsSettleDoesNotTurnOnHowCaseNamesCompareTest {

    /**
     * A body deciding on what one dependency answers, whose points of {@code id > 5} ask nothing
     * about which case the answer is.
     *
     * <p>A row composed for one of those points is free at the case, and what it takes below the
     * {@code match} follows from what it was given there.
     */
    private static final String MODEL = """
            module example.spelling

            data Yes
            data No
            data Answer = Yes | No

            data Blocked = Int
            data Cleared = { ok: Bool }

            behavior lookup : (id: Int) -> Blocked | Cleared

            behavior decides : (id: Int) -> Answer
                depends on lookup
            let decides (id, lookup) =
                if id > 5 then
                    match lookup(id) with
                        | Blocked -> No
                        | Cleared { ok } -> if ok then Yes else No
                else No

            example decides
                | (0) with lookup = Blocked(1) -> No
            """;

    /**
     * And a body whose line is drawn inside one of the cases.
     *
     * <p>A point of that line is a place the input stands at and says nothing about what the
     * dependency answers — but a row only arrives there through the case the line is written in, so
     * which case a row composed for the point carries decides whether the point is reached at all.
     */
    private static final String BEHIND_A_CASE = """
            module example.behind

            data Yes
            data No
            data Answer = Yes | No

            data Blocked = Int
            data Cleared = { ok: Bool }

            behavior lookup : (id: Int) -> Blocked | Cleared

            behavior decides : (id: Int) -> Answer
                depends on lookup
            let decides (id, lookup) =
                match lookup(id) with
                    | Blocked -> No
                    | Cleared { ok } -> if id > 5 then Yes else No

            example decides
                | (0) with lookup = Blocked(1) -> No
            """;

    private static final String EITHER_REACHES = """
            module example.either

            data Yes
            data No
            data Answer = Yes | No

            data Blocked = { ok: Bool }
            data Cleared = { ok: Bool }

            behavior lookup : (id: Int) -> Blocked | Cleared

            behavior decides : (id: Int) -> Answer
                depends on lookup
            let decides (id, lookup) =
                if id > 5 then
                    match lookup(id) with
                        | Blocked { ok } -> if ok then Yes else No
                        | Cleared { ok } -> if ok then No else Yes
                else No

            example decides
                | (0) with lookup = Blocked { ok = true } -> No
            """;

    /** The same names at the same width, comparing the other way round. */
    private static final Map<String, String> THE_OTHER_WAY = Map.of(
            "Blocked", "Refused",
            "Cleared", "Allowed");

    /** And the same names at the same width, comparing the way they already did. */
    private static final Map<String, String> THE_SAME_WAY = Map.of(
            "Blocked", "Barring",
            "Cleared", "Cutting");

    @Test
    void oneModelSpelledTwoWaysSettlesTheSameObligations() {
        Set<String> asWritten = settledBy(MODEL);
        Set<String> respelled = settledUnder(MODEL, THE_OTHER_WAY);

        assertFalse(asWritten.isEmpty(), "the offering settles something to compare");
        assertEquals(List.of(), onlyOneSpellingSettles(asWritten, respelled),
                "an obligation settled under one spelling of the cases and not the other");
    }

    /**
     * And the same where either case reaches the point, and what each goes on to do below it
     * differs.
     *
     * <p>A row offered for a point answers whatever else it turns out to answer, so two rows that
     * both stand at the point are not interchangeable: one goes down one case and the other down
     * the other. What is held is that the offering settles the same obligations whichever of them
     * the search is written with.
     */
    @Test
    void eitherCaseReachingThePointSettlesTheSameObligations() {
        Set<String> asWritten = settledBy(EITHER_REACHES);
        Set<String> respelled = settledUnder(EITHER_REACHES, THE_OTHER_WAY);

        assertFalse(asWritten.isEmpty(), "the offering settles something to compare");
        assertEquals(List.of(), onlyOneSpellingSettles(asWritten, respelled),
                "an obligation settled under one spelling of the cases and not the other");
    }

    /** And the same where what a row has to carry to reach a point is the case it stands in. */
    @Test
    void aPointBehindACaseIsSettledUnderEitherSpelling() {
        Set<String> asWritten = settledBy(BEHIND_A_CASE);
        Set<String> respelled = settledUnder(BEHIND_A_CASE, THE_OTHER_WAY);

        assertFalse(asWritten.isEmpty(), "the offering settles something to compare");
        assertEquals(List.of(), onlyOneSpellingSettles(asWritten, respelled),
                "an obligation settled under one spelling of the cases and not the other");
    }

    /**
     * And a spelling the names compare the same way under settles the same, which is what says the
     * comparison is what the other one moved.
     *
     * <p>Without this, a difference there would be a difference between two models with different
     * words in them, and which of the words did it would be the reader's guess.
     */
    @Test
    void aSpellingThatComparesTheSameWayIsTheSameOffering() {
        assertEquals(List.of(), onlyOneSpellingSettles(settledBy(MODEL),
                        settledUnder(MODEL, THE_SAME_WAY)),
                "the names were exchanged and the order they compare in was not");
    }

    /** The obligations the rows offered over the module settle, as this walk reads them. */
    private static Set<String> settledBy(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        String module = compilation.modules().get(0);
        Map<String, Adequacy.Filling> filled = Adequacy.generatedOf(compilation.db(), module);
        assertTrue(filled != null && !filled.isEmpty(), "the module is offered rows");
        Composition offering = Composition.composed(OfferingRequest.overTheModule(module), filled,
                Adequacy.accountFor(compilation.db(), module, new GenerationScope.Module()));
        Settlements settlements = Settlements.of(compilation.db(), offering);
        Set<String> out = new TreeSet<>();
        for (ObligationIdentity item : settlements.settled()) {
            out.add(String.valueOf(item));
        }
        return out;
    }

    /**
     * What one spelling settles and the other does not, either way round.
     *
     * <p>The difference rather than the two sets, because an obligation is written out in full here
     * and a reader is owed the ones that moved rather than every one that did not.
     */
    private static List<String> onlyOneSpellingSettles(Set<String> asWritten,
                                                      Set<String> respelled) {
        List<String> out = new ArrayList<>();
        asWritten.stream().filter(each -> !respelled.contains(each))
                .forEach(each -> out.add("only as written: " + each));
        respelled.stream().filter(each -> !asWritten.contains(each))
                .forEach(each -> out.add("only respelled: " + each));
        return out;
    }

    /** What the model settles under {@code spelling}, said in the names the model is written in. */
    private static Set<String> settledUnder(String written, Map<String, String> spelling) {
        String model = written;
        for (Map.Entry<String, String> each : spelling.entrySet()) {
            model = model.replace(each.getKey(), each.getValue());
        }
        Set<String> out = new TreeSet<>();
        for (String each : settledBy(model)) {
            String said = each;
            for (Map.Entry<String, String> pair : spelling.entrySet()) {
                said = said.replace(pair.getValue(), pair.getKey());
            }
            out.add(said);
        }
        return out;
    }
}
