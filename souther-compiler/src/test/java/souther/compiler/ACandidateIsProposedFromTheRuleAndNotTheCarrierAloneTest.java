package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.Generator;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a position offers, once the rules written on its type are read before the value is chosen.
 *
 * <p>A representative used to come from the carrier alone — the empty one for every collection, a
 * one-character string — and the rules were consulted only afterwards, by the decoder that refuses
 * what was built. A rule saying a collection is not empty is then the one rule that refuses the one
 * value on offer, and since a row is the product of its positions, one such field took every row of
 * the behavior with it.
 *
 * <p>A candidate is still a proposal the decoder answers. Nothing here claims a witness exists for an
 * arbitrary rule: what is held to is narrower — a minimum this can read is a minimum the candidate is
 * built at, rather than one the choice is made in ignorance of.
 */
class ACandidateIsProposedFromTheRuleAndNotTheCarrierAloneTest {

    /**
     * A model whose one uncovered combination needs a value of the constrained type.
     *
     * <p>{@code t.kind} is divided into two and one of them has a row, so the row that is owed is the
     * other one — and writing it takes a {@code tags} the type admits.
     */
    private static String model(String declaration, String field, String written) {
        return """
                module nd.gen

                data Domestic
                data Overseas
                data Kind = Domestic | Overseas

                %s

                data T = { kind: Kind, %s }

                behavior look : (t: T) -> Int

                let look (t) = 1

                example look
                    | (T { kind = Domestic, %s }) -> 1
                """.formatted(declaration, field, written);
    }

    /** The one row the generator writes for that combination, as the text an author is offered. */
    private static String generatedRow(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all = compilation.db()
                .ask(new Adequacy.Generated(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        Generator.GenerationResult filled = all.get("look").pairs();
        assertEquals(List.of(), filled.unresolved(),
                "the combination is one a value exists for, so nothing is left unresolved");
        assertEquals(1, filled.rows().size(), "one combination is uncovered, so one row is written");
        return filled.rows().get(0).inputs().get(0).text();
    }

    // --- a collection the rules say is not empty ---------------------------------------------------

    @Test
    void aListTheRuleSaysIsNotEmptyIsOfferedAnElement() {
        String row = generatedRow(model("""
                data Tag = List<String>
                    invariant someTags = List.length(value) >= 1
                """, "tags: Tag", "tags = Tag([\"t\"])"));

        assertEquals("T { kind = Overseas, tags = Tag([\"x\"]) }", row);
    }

    /**
     * The minimum itself, and not one element.
     *
     * <p>A reader that recognised {@code >= 3} and then offered a list of one would refuse the row for
     * the same reason it refused the empty one, having read the rule and not used it.
     */
    @Test
    void aListIsOfferedAsManyElementsAsTheMinimumNames() {
        String row = generatedRow(model("""
                data Tags = List<String>
                    invariant enough = List.length(value) >= 3
                """, "tags: Tags", "tags = Tags([\"a\", \"b\", \"c\"])"));

        assertEquals("T { kind = Overseas, tags = Tags([\"x\", \"x\", \"x\"]) }", row);
    }

    /**
     * A set counts what a list does, and its rule is read the same way.
     *
     * <p>Which the decoder's own reading cannot supply. Raoh has no constraint for a set's size — a
     * set crosses the boundary as a list, so a size chained after the mapping that drops duplicates
     * would count the wrong things — and a candidate chooser reading the decoder's constraints would
     * find nothing here.
     */
    @Test
    void aSetTheRuleSaysIsNotEmptyIsOfferedAnElement() {
        String row = generatedRow(model("""
                data Codes = Set<String>
                    invariant someCodes = Set.size(value) >= 1
                """, "codes: Codes", "codes = Codes([\"c\"])"));

        assertEquals("T { kind = Overseas, codes = Codes([\"x\"]) }", row);
    }

    /** A set of three is three elements no two of which are equal, or it is a set of fewer. */
    @Test
    void aSetIsOfferedElementsNoTwoOfWhichAreEqual() {
        String row = generatedRow(model("""
                data Codes = Set<String>
                    invariant enough = Set.size(value) >= 3
                """, "codes: Codes", "codes = Codes([\"a\", \"b\", \"c\"])"));

        assertEquals("T { kind = Overseas, codes = Codes([\"x\", \"xx\", \"xxx\"]) }", row);
    }

    @Test
    void aMapTheRuleSaysIsNotEmptyIsOfferedAnEntry() {
        String row = generatedRow(model("""
                data Props = Map<String, String>
                    invariant someProps = Map.size(value) >= 1
                """, "props: Props", "props = Props([(\"k\", \"v\")])"));

        assertEquals("T { kind = Overseas, props = Props([(\"x\", \"x\")]) }", row);
    }

    /** Two entries is two keys no two of which are equal; the values under them are free to repeat. */
    @Test
    void aMapIsOfferedEntriesNoTwoOfWhichShareAKey() {
        String row = generatedRow(model("""
                data Props = Map<String, String>
                    invariant enough = Map.size(value) >= 2
                """, "props: Props", "props = Props([(\"k\", \"v\"), (\"l\", \"w\")])"));

        assertEquals("T { kind = Overseas, props = Props([(\"x\", \"x\"), (\"xx\", \"x\")]) }", row);
    }

    // --- a string the rules give a length ----------------------------------------------------------

    /**
     * The fixed {@code "x"} is a string of one, so a minimum of one was met by accident and a minimum
     * of two was not. Both are here: the first has to keep working and the second is the defect.
     */
    @Test
    void aStringIsOfferedALengthTheMinimumAdmits() {
        String row = generatedRow(model("""
                data Name = String
                    invariant longEnough = String.length(value) >= 5
                """, "name: Name", "name = Name(\"abcde\")"));

        assertEquals("T { kind = Overseas, name = Name(\"xxxxx\") }", row);
    }

    @Test
    void aStringWhoseMinimumIsOneIsStillOfferedTheOneCharacterValue() {
        String row = generatedRow(model("""
                data Name = String
                    invariant longEnough = String.length(value) >= 1
                """, "name: Name", "name = Name(\"abcde\")"));

        assertEquals("T { kind = Overseas, name = Name(\"x\") }", row);
    }

    /**
     * A format and a minimum are two proposals, not a precedence.
     *
     * <p>The shortest string the pattern accepts is the empty one, which the minimum refuses; the
     * string the minimum asks for is five characters, which this pattern accepts. A reader that took
     * the format as the answer wherever there was one would offer only the first and report the
     * combination as refused. Neither candidate is a claim — what settles it is that the decoder was
     * given both to answer.
     */
    @Test
    void aFormatAndAMinimumAreBothProposedAndTheDecoderChooses() {
        String row = generatedRow(model("""
                data Tag = String
                    invariant shaped = String.matches("x*", value)
                    invariant longEnough = String.length(value) >= 5
                """, "tag: Tag", "tag = Tag(\"xxxxx\")"));

        assertEquals("T { kind = Overseas, tag = Tag(\"xxxxx\") }", row);
    }

    // --- what a rule reaches -----------------------------------------------------------------------

    /**
     * The elements have rules of their own, and the value inside the collection is built against them.
     *
     * <p>A witness is a tree: what stands for a list is a list of what stands for its element, which
     * is itself a value some rule may have something to say about.
     */
    @Test
    void anElementsOwnRuleIsReadWhereTheElementIsBuilt() {
        String row = generatedRow(model("""
                data Word = String
                    invariant longEnough = String.length(value) >= 4

                data Words = List<Word>
                    invariant someWords = List.length(value) >= 1
                """, "words: Words", "words = Words([Word(\"abcd\")])"));

        assertEquals("T { kind = Overseas, words = Words([Word(\"xxxx\")]) }", row);
    }

    /**
     * An element offering several values offers all of them to the collection built around it.
     *
     * <p>Which is the same thing the position itself is owed, one level down. {@code Word} proposes the
     * shortest string its format accepts and the string its minimum asks for, and the decoder settles
     * which; a list that took the first of those and stopped would report the combination as refused
     * while a list of the second is a value the model plainly admits. Collapsing the element to one
     * value moves the defect this whole change is about from the collection to what it holds.
     */
    @Test
    void anElementOfferingSeveralValuesOffersThemAllThroughTheCollection() {
        String row = generatedRow(model("""
                data Word = String
                    invariant shaped = String.matches("x*", value)
                    invariant longEnough = String.length(value) >= 5

                data Words = List<Word>
                    invariant someWords = List.length(value) >= 1
                """, "words: Words", "words = Words([Word(\"xxxxx\")])"));

        assertEquals("T { kind = Overseas, words = Words([Word(\"xxxxx\")]) }", row);
    }

    /** The same of what a map holds under its keys. */
    @Test
    void aValueOfferingSeveralOfThemOffersThemAllThroughTheMap() {
        String row = generatedRow(model("""
                data Word = String
                    invariant shaped = String.matches("x*", value)
                    invariant longEnough = String.length(value) >= 5

                data Words = Map<String, Word>
                    invariant someWords = Map.size(value) >= 1
                """, "words: Words", "words = Words([(\"k\", Word(\"xxxxx\"))])"));

        assertEquals("T { kind = Overseas, words = Words([(\"x\", Word(\"xxxxx\"))]) }", row);
    }

    /**
     * Elements that differ are elements of the type, not numbers counted from nothing.
     *
     * <p>A set of two needs a second value no rule of the element refuses. Counting {@code 0, 1, 2} for
     * distinctness offers a number the element's own bound rejects, and the set is then refused for the
     * element rather than for anything about its size — the same collapse as above, arrived at from the
     * other side.
     */
    @Test
    void aSetsSecondElementComesFromInsideTheElementsOwnBound() {
        String row = generatedRow(model("""
                data Positive = Int
                    invariant atLeastTen = value >= 10

                data Positives = Set<Positive>
                    invariant enough = Set.size(value) >= 2
                """, "ns: Positives", "ns = Positives([Positive(10), Positive(11)])"));

        assertEquals("T { kind = Overseas, ns = Positives([Positive(10), Positive(11)]) }", row);
    }

    /**
     * The same of a map's keys, which have to differ for the same reason.
     *
     * <p>Keyed by a string, because a map that crosses the boundary is a JSON object and its keys are
     * strings (<<e1314>>). The rule the second key has to keep is its length rather than a bound, and
     * it is the same question: a key made without reading the key's own rules is a key the map is
     * refused for.
     */
    @Test
    void aMapsSecondKeyComesFromInsideTheKeysOwnRules() {
        String row = generatedRow(model("""
                data Code = String
                    invariant longEnough = String.length(value) >= 3

                data ByCode = Map<Code, String>
                    invariant enough = Map.size(value) >= 2
                """, "by: ByCode", "by = ByCode([(Code(\"aaa\"), \"a\"), (Code(\"bbbb\"), \"b\")])"));

        assertEquals("T { kind = Overseas, by = ByCode([(Code(\"xxx\"), \"x\"), "
                + "(Code(\"xxxx\"), \"x\")]) }", row);
    }

    /**
     * A type written in terms of itself is what the descent gives up on.
     *
     * <p>No value of it exists, so the giving up is the right answer and not a limit reached. What
     * matters is that it is reported the way any other refusal is, rather than descending forever.
     */
    @Test
    void aTypeWrittenInTermsOfItselfIsGivenUpOn() {
        String source = model("""
                data Nest = List<Nest>
                    invariant someNest = List.length(value) >= 1
                """, "nest: Nest", "nest = Nest([])");
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();

        assertNotNull(compilation.db().ask(new Adequacy.Generated(compilation.modules().get(0)))
                .value(), "asking for the rows comes back rather than descending forever");
    }

    /**
     * A chain of names is not a type written in terms of itself.
     *
     * <p>What the descent has to give up on is a value inside itself, and how many names a value wears
     * on the way down is not that. A count of levels cannot tell the two apart, so it is the names being
     * expanded that say when to stop.
     */
    @Test
    void aLongChainOfNamesIsStillBuilt() {
        String row = generatedRow(model("""
                data L1 = String
                data L2 = L1
                data L3 = L2
                data L4 = L3
                data L5 = L4

                data Deep = List<L5>
                    invariant someDeep = List.length(value) >= 1
                """, "deep: Deep", "deep = Deep([L5(L4(L3(L2(L1(\"a\")))))])"));

        assertEquals("T { kind = Overseas, deep = Deep([L5(L4(L3(L2(L1(\"x\")))))]) }", row);
    }

    /**
     * A rule the reader has nothing to say about leaves the position where it was.
     *
     * <p>The guarantee is that a minimum this recognises is used, not that a witness is found for
     * whatever anyone writes. A rule of a shape nothing here reads still refuses every candidate, and
     * that is still reported as a refusal rather than as a combination nobody can write a row for.
     */
    @Test
    void aRuleNothingHereReadsStillLeavesTheCombinationRefusedAndSaidSo() {
        String source = model("""
                data Tags = List<String>
                    invariant distinct = List.allDistinctBy(x -> x, value)
                        && List.length(value) >= 2
                    invariant notTwo = List.length(value) /= 2
                """, "tags: Tags", "tags = Tags([\"a\", \"b\", \"c\"])");
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all = compilation.db()
                .ask(new Adequacy.Generated(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        Generator.GenerationResult filled = all.get("look").pairs();

        assertEquals(List.of(), filled.rows(), "two equal elements is not a list of two distinct ones");
        assertTrue(filled.unresolved().stream().allMatch(left ->
                        left.reason() == Generator.UnresolvedCombination.Reason
                                .ALL_CANDIDATES_REJECTED),
                "refused, which is not a claim that no row can be written: "
                        + filled.unresolved());
    }

    // --- the row as text ---------------------------------------------------------------------------

    /**
     * A row is offered as text for somebody to paste into a model, so the text has to come back as the
     * value it was built from. Held against the compiler rather than against a spelling: a template
     * that prints a map entry a reader does not accept would satisfy every assertion above.
     */
    @Test
    void theTextOfAGeneratedRowIsAnExampleThatCompiles() {
        String declarations = """
                data Tags = List<String>
                    invariant someTags = List.length(value) >= 2

                data Codes = Set<String>
                    invariant someCodes = Set.size(value) >= 2

                data Props = Map<String, String>
                    invariant someProps = Map.size(value) >= 2

                data Name = String
                    invariant longEnough = String.length(value) >= 3
                """;
        String fields = "tags: Tags, codes: Codes, props: Props, name: Name";
        String written = "tags = Tags([\"a\", \"b\"]), codes = Codes([\"a\", \"b\"]), "
                + "props = Props([(\"k\", \"v\"), (\"l\", \"w\")]), name = Name(\"abc\")";
        String row = generatedRow(model(declarations, fields, written));

        String withTheRow = model(declarations, fields, written)
                + "    | (" + row + ") -> 1\n";
        Compilation again = Compilation.ofSource(withTheRow, "Main");
        again.answerEverything();

        assertEquals(List.of(), again.diagnostics().values().stream().flatMap(List::stream).toList(),
                "the generated row is written the way a fixture is read: " + row);
    }
}
