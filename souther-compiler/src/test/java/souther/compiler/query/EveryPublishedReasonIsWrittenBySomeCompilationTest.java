package souther.compiler.query;

import souther.compiler.diag.SourceRendering;
import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.check.ReadingPolicy;
import souther.compiler.partition.AdequacyPolicy;
import souther.compiler.partition.Budgets;
import souther.compiler.partition.UndividedPosition;
import souther.compiler.regex.PatternPlan;
import souther.compiler.report.AdequacyReport;
import souther.compiler.values.AsACompilationAllows;

import java.util.EnumMap;
import java.util.EnumSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every reason this compiler may publish is one a compilation of it writes into a document.
 *
 * <p>Two fields carry the vocabulary: {@code notRead}, under a position, and what stopped the
 * reading of a rule an offer of values got nothing from
 * ({@code synthesisShortfallCauses[].unread}). The second is the first's words said of a rule, so a word either of them writes is a word of the
 * vocabulary kept — read off one of them alone, a word only the other writes would arrive here as
 * a promise nothing keeps.
 *
 * <p>A published word is a promise to a reader that there is a state of the model this compiler
 * answers with it. Nothing else here holds that promise: the writer and the schema are held to each
 * other, and two sides agreeing about a shape neither has been asked to produce agree about
 * anything — a word can be spelled the same in both and name a state no compilation reaches, and
 * every sentence written about it goes on being written with nothing to check it against.
 *
 * <p><b>Against a document and not against the stage that decides.</b> A stage answering with the
 * reason is what its own test says; whether the answer survives the projection to the published
 * vocabulary and the writer is what this says, and those are the two edges a word travels that
 * nothing else was reading.
 *
 * <p><b>Total over what this compiler can write, by the machine and not by a list beside it.</b> A
 * word added to {@link UndividedPosition.Reason} arrives here as a word with no model, which is the
 * question being asked of whoever added it. There is no arm for a word nobody can reach: a reason
 * nothing produces is one to take out of the vocabulary or to give a way in, and an entry saying so
 * would make this test agree that a promise need not be kept.
 *
 * <p><b>Which is narrower than what the schema admits, by one word.</b> The field's vocabulary out
 * there also holds the walk stopping after a count of steps, which nothing writes any more and
 * which no reason of this compiler projects to — a word documents of this version carry because
 * they were written before it stopped being written, kept and accounted for where the two surfaces
 * are held to their own producers
 * ({@code WhatEachWayOfDrawingNoLineLeavesIsWrittenDownOnceTest}). Enumerated here as well, it
 * would arrive as a word owed a model no compilation can make — and the arm that would let it pass
 * is the one this has none of.
 *
 * <p><b>Named for the vocabulary and not for either field.</b> {@code notRead} is the document's
 * word and it is wider than the word: a rule read from end to end that draws no line is written
 * there too, and nothing in this compiler calls such a rule one it could not read
 * ({@link PartitionEvidence.NotRead}). So what these models are held to reach is the published
 * vocabulary, and a name saying "unread" would lose a distinction the reasons themselves are split
 * by — a reading that stopped and a rule read to the end are separate capabilities of
 * {@link BlockReason}, and having been one is what that split was made after.
 *
 * <p><b>A model here need not compile without a diagnostic.</b> What is claimed is that a
 * compilation writes the word, and this compiler writes an adequacy document about a model it has
 * something to say against — a declaration nothing can construct and a clause the front end could
 * not type are both such models, and the words for them are among what these are here to reach.
 *
 * <p>A word arriving in the vocabulary leaves the schema's version where it was, and the schema
 * says why in its own words: a word added to an enumerated field is one no earlier document
 * carried, so a document written before it existed is still a document of this version. So what an
 * arrival owes is a model here, and not a version.
 */
class EveryPublishedReasonIsWrittenBySomeCompilationTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * A model, and what a compilation of it may spend.
     *
     * @param source    the module handed over
     * @param allowance what it is read under, which is one thing and not a pair of settings a
     *                  caller might leave both of
     */
    private record Witness(String source, Allowance allowance) {}

    /**
     * What a compilation of a model here is allowed.
     *
     * <p>One of three and not two nullable settings beside each other. Two settings admit a fourth
     * state nothing here means — a model read under both at once — and a reader of the record would
     * have to find the three factories to learn that it never happens.
     */
    private sealed interface Allowance {

        /** What a compilation says, which is what all but two of these are read under. */
        record AsACompilationDoes() implements Allowance {}

        /** What a measure may spend working out what a behavior's rules tell apart. */
        record ToMeasureWith(PatternPlan.Budget distinctions) implements Allowance {}

        /** What a reading of the declarations may build with. */
        record ToReadWith(ReadingPolicy reading) implements Allowance {}
    }

    private static Witness of(String source) {
        return new Witness(source, new Allowance.AsACompilationDoes());
    }

    /** {@code t0 = 0.1m} and each {@code tN} the square of the one before it, so that the scale
     *  doubles at each step. */
    private static String squaringsOfATenth(int times) {
        StringBuilder lets = new StringBuilder("let t0 = 0.1m\n");
        for (int i = 1; i <= times; i++) {
            lets.append("let t").append(i).append(" = sq(t").append(i - 1).append(")\n");
        }
        return lets.toString();
    }

    /**
     * A model read under an allowance said down, which is how the two words for something costing
     * more than this compiler spends are reached.
     *
     * <p>Not a larger model. Every default is set with room over anything anybody would write here,
     * so a model built to exhaust one would be built against the figure rather than against what
     * the word says — and what a compilation may spend is the compilation's to say, which is what
     * these two ask of it.
     *
     * <p>That the allowance is what reaches them is not left to this sentence:
     * {@link #neitherCostlyWordIsWrittenAtWhatACompilationAllows} reads the same models under what
     * a compilation says and holds them to writing neither word.
     */
    private static Witness spending(String source, PatternPlan.Budget distinctions) {
        return new Witness(source, new Allowance.ToMeasureWith(distinctions));
    }

    /** The same, where what is said down is what a reading of the declarations may build with. */
    private static Witness readingWith(String source, ReadingPolicy reading) {
        return new Witness(source, new Allowance.ToReadWith(reading));
    }

    /** Room to answer what a position admits, and none to hand each of its rules on as the set it
     *  leaves — which is the second of the two shortfalls one word covers. */
    private static final ReadingPolicy NOTHING_TO_HAND_ON_WITH = new ReadingPolicy(
            ReadAs.THE_COMPILATION_DOES.dnfExpansionLimit(),
            ReadAs.THE_COMPILATION_DOES.scalePlacesLimit(),
            AsACompilationAllows.admittedValues(),
            new PatternPlan.Budget(1, 1, 1_000_000_000L));

    /** The answers, and the units a behavior over them is written to return. */
    private static final String ANSWER = """
            data Yes
            data No
            data Answer = Yes | No
            """;

    private static Map<UndividedPosition.Reason, Witness> witnesses() {
        Map<UndividedPosition.Reason, Witness> out =
                new EnumMap<>(UndividedPosition.Reason.class);
        // A comparison whose other side is not a form a threshold is read out of. Every part of it
        // was seen; what has no reading is the shape, which is something an author can write
        // differently.
        out.put(UndividedPosition.Reason.UNSUPPORTED_SYNTAX, of("""
                module m
                %s
                behavior f : (n: Int) -> Answer
                let f (n) = if n * n > 4 then Yes else No
                """.formatted(ANSWER)));
        // A rule whose end at a position rests on an alternative this compiler does not read. The
        // clause at the position was read and places its end; what the choice leaves is as far out
        // as the branch beside it allows, and that branch is a form no reading here enters.
        out.put(UndividedPosition.Reason.UNREAD_ALTERNATIVE_OF_A_CHOICE, of("""
                module m
                %s
                data N = { n: Int }
                    invariant r = n >= 2 || Int.abs(n) >= 5

                behavior f : (v: N) -> Answer
                let f (v) = Yes
                """.formatted(ANSWER)));
        // A clause nothing could type, which never reaches a reading — so which position it governs
        // is exactly what is unknown about it. The other way to the same hole is a declaration that
        // resolves while nothing expands the clauses of its module
        // ({@link souther.compiler.AnExpansionThatDidNotHappenIsARuleNotReachedTest}); one model
        // apiece would say the word belongs to the route rather than to the hole.
        out.put(UndividedPosition.Reason.RULES_NOT_READ_AT_ALL, of("""
                module m

                data Ok
                data Item = String
                    invariant unreadable = value == 1
                data Basket = { item: Item }

                behavior run : (b: Basket) -> Ok
                let run (b) = Ok
                """));
        // A position whose own answer is exact and whose rules were not handed on as the sets they
        // leave. What the rules say is contradictory, which is the model's business and not this
        // word's: the word is about the second allowance, and it is the allowance that is lowered.
        out.put(UndividedPosition.Reason.EXACT_VALUES_TOO_COSTLY, readingWith("""
                module m

                data Code = String
                    invariant named = value == "x"
                    invariant other = value /= "x"
                    invariant format = String.matches("[A-Z]{2}", value)

                data Ok

                behavior f : (c: Code) -> Ok
                """, NOTHING_TO_HAND_ON_WITH));
        // A behavior's rule about the strings at a position, under an allowance that will not build
        // the two sides of one rule. Its own word beside the one above because that one is what the
        // declarations leave and this is what a body tells apart.
        out.put(UndividedPosition.Reason.BEHAVIOR_DISTINCTIONS_TOO_COSTLY, spending("""
                module m
                %s
                behavior route : (code: String) -> Answer
                let route (code) = if String.startsWith("JP", code) then Yes else No
                """.formatted(ANSWER), new PatternPlan.Budget(1, 1, 1_000_000_000L)));
        // Values no line can be drawn on: two booleans are equal or they are not, and neither is
        // above the other.
        out.put(UndividedPosition.Reason.UNSUPPORTED_DOMAIN, of("""
                module m
                %s
                behavior f : (a: Bool, b: Bool) -> Answer
                let f (a, b) = if a == b then Yes else No
                """.formatted(ANSWER)));
        // A line that falls at a number no exact ratio holds. A tenth squared sixty-three times is
        // the least exponent a ratio has, and a rule weighing a position by it puts the line at a
        // number past the other end. The values carry an order and the rule is written to the end,
        // so this is not the word above.
        out.put(UndividedPosition.Reason.LINE_AT_A_NUMBER_NO_RATIO_HOLDS, of("""
                module m
                %s
                let sq (x: Decimal): Decimal = x * x
                %s
                data A = Decimal
                data H = { a: A }

                behavior f : (h: H) -> Answer
                let f (h) = if t63 * h.a.value <= 1.0m then Yes else No
                """.formatted(ANSWER, squaringsOfATenth(63))));
        // A line that is placed, with a value beside it that was not worked out. One squaring fewer
        // puts the line at a number a ratio holds and the whole number beside it past what the host
        // builds the digits of. The rule is written to the end and its line has a place, so this is
        // not the word above.
        out.put(UndividedPosition.Reason.LINE_SIDE_NOT_WORKED_OUT, of("""
                module m
                %s
                let sq (x: Decimal): Decimal = x * x
                %s
                data A = Decimal
                data H = { a: A }

                behavior f : (h: H) -> Answer
                let f (h) = if t62 * h.a.value <= 1.0m then Yes else No
                """.formatted(ANSWER, squaringsOfATenth(62))));
        // Each name of the line stands at a position under every case of the sum, and which of
        // those pair off is what nothing worked out. The record both cases spread is what puts one
        // name at more than one position while leaving the field writable without a match.
        out.put(UndividedPosition.Reason.UNRESOLVED_CASE_PAIRING, of("""
                module m
                %s
                data Bounds = { lo: Int, hi: Int }
                data Small = { ...Bounds }
                data Large = { ...Bounds }
                data P = Small | Large

                behavior f : (p: P) -> Answer
                let f (p) = if p.lo < p.hi then Yes else No
                """.formatted(ANSWER)));
        // What the rule states is read through what the operation answers in each of its cases,
        // and comes to one line or another — and one of them is over a value the body made rather
        // than the input's own numbers, so none of its lines is drawn.
        out.put(UndividedPosition.Reason.SEVERAL_LINES_IN_ONE_RULE, of("""
                module m
                %s
                behavior f : (a: Int, b: Int, c: Int) -> Answer
                let f (a, b, c) = {
                    let p = a * b
                    if Int.max(p, c) > 5 then Yes else No
                }
                """.formatted(ANSWER)));
        // The same operation over the input's own numbers draws a line for each relation, and the
        // line on a decides nothing any row reaches: wherever a passes five, a + n is past it too.
        out.put(UndividedPosition.Reason.RULE_NEVER_TURNS_ON_THIS_LINE, of("""
                module m
                %s
                data N = Int
                    invariant value >= 1

                behavior f : (a: Int, n: N) -> Answer
                let f (a, n) = if Int.max(a, a + n.value) > 5 then Yes else No
                """.formatted(ANSWER)));
        // A line between two positions, which divides neither.
        out.put(UndividedPosition.Reason.UNSUPPORTED_PARTITION_SHAPE, of("""
                module m
                %s
                behavior f : (a: Int, b: Int) -> Answer
                let f (a, b) = if a < b then Yes else No
                """.formatted(ANSWER)));
        // And a line on a number taken over a run of the values at a position rather than on any
        // one of them: two of them either side of a total are on the line as surely as one is.
        out.put(UndividedPosition.Reason.RULE_ABOUT_A_RUN, of("""
                module m
                %s
                data Line = { v: Int }
                data Bag = { lines: List<Line>, cap: Int }

                let total (lines: List<Line>): Int = List.sum(List.map(one -> one.v, lines))

                behavior f : (bag: Bag) -> Answer
                let f (bag) = if total(bag.lines) > bag.cap then Yes else No
                """.formatted(ANSWER)));
        // A denial says which values exist rather than where they stop, so it holds the position to
        // what it admits and places no end on it.
        out.put(UndividedPosition.Reason.POSITION_RESTRICTED_TO_WHAT_A_RULE_ADMITS, of("""
                module m
                %s
                data N = Int
                    invariant value /= 5

                behavior f : (n: N) -> Answer
                let f (n) = Yes
                """.formatted(ANSWER)));
        // The walk reaches this declaration again under itself, so what stands below is what stands
        // below the one it already read.
        out.put(UndividedPosition.Reason.RETURNS_TO_A_DECLARATION_ALREADY_READ, of("""
                module m
                %s
                data Node = { next: Node?, n: Int }

                behavior f : (node: Node) -> Answer
                let f (node) = if node.n > 3 then Yes else No
                """.formatted(ANSWER)));
        // A newtype spine that comes back to itself: the walk over the names ends with the name
        // still on, so there is no base to read a shape from.
        out.put(UndividedPosition.Reason.TYPE_UNRESOLVED, of("""
                module m

                data Ok
                data Cyclic = Cyclic

                behavior run : (x: Cyclic) -> Ok
                let run (x) = Ok
                """));
        // A rule about a value an operation made of the positions. Where the value came from is
        // known; what the rule says about the values at either position is not, because the minutes
        // between two moments are not the difference of the two counts.
        out.put(UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE, of("""
                module m
                %s
                behavior f : (a: DateTime, b: DateTime) -> Answer
                let f (a, b) = if DateTime.minutesBetween(a, b) > 10 then Yes else No
                """.formatted(ANSWER)));
        // One block written once and handed to two walks. The name it reads the element under
        // holds an element of a different container on each run, so the rule inside it is about one
        // of the two and nothing here says which — and each of them is told so.
        out.put(UndividedPosition.Reason.RULE_ABOUT_AN_ELEMENT_OF_SEVERAL_CONTAINERS, of("""
                module m
                %s
                behavior f : (xs: List<Int>, ys: List<Int>) -> Answer
                let f (xs, ys) = {
                    let positive = (x) -> x > 0
                    if List.any(positive, xs) && List.any(positive, ys) then Yes else No
                }
                """.formatted(ANSWER)));
        // Read to the end, and the positions cancel: the rule is about the position and the
        // quantity it cuts is nothing.
        out.put(UndividedPosition.Reason.RULE_CUTS_NOTHING, of("""
                module m
                %s
                behavior f : (a: Int) -> Answer
                let f (a) = if a - a <= 0 then Yes else No
                """.formatted(ANSWER)));
        // Every string begins with the empty one, so the rule puts every value the position holds
        // on one side of itself and the model draws no line between any two of them.
        out.put(UndividedPosition.Reason.RULE_TELLS_NOTHING_APART, of("""
                module m
                %s
                behavior route : (code: String) -> Answer
                let route (code) = {
                    guard String.startsWith("", code) else No
                    Yes
                }
                """.formatted(ANSWER)));
        // A line on the order the strings are counted on beside a set of them told from the rest.
        // A class in one cannot be written in the other, so the position has no single list of
        // classes while both rules stand.
        out.put(UndividedPosition.Reason.CLASSES_NOT_COMPOSED, of("""
                module m
                %s
                behavior route : (code: String) -> Answer
                let route (code) = {
                    guard String.startsWith("JP", code) else No
                    guard code < "M" else No
                    Yes
                }
                """.formatted(ANSWER)));
        // A line where the quantity it cuts never runs: the declaration holds the number at or
        // above nought, and the rule compares it against a negative.
        out.put(UndividedPosition.Reason.RULE_CUTS_OUTSIDE_WHAT_THE_QUANTITY_HOLDS, of("""
                module m
                %s
                data N = Int
                    invariant value >= 0

                behavior f : (n: N) -> Answer
                let f (n) = if n.value < 0 - 5 then Yes else No
                """.formatted(ANSWER)));
        // A comparison over nine values each chosen by cases, read once for each way the cases
        // can fall: more readings than one condition is read on.
        out.put(UndividedPosition.Reason.RULE_MEANING_NOT_READ, of("""
                module m
                %s
                behavior f : (n: Int) -> Answer
                let f (n) = {
                    let a = if n > 1 then 1 else 0
                    let b = if n > 2 then 1 else 0
                    let c = if n > 3 then 1 else 0
                    let d = if n > 4 then 1 else 0
                    let e = if n > 5 then 1 else 0
                    let g = if n > 6 then 1 else 0
                    let h = if n > 7 then 1 else 0
                    let i = if n > 8 then 1 else 0
                    let j = if n > 9 then 1 else 0
                    if a + b + c + d + e + g + h + i + j > n then Yes else No
                }
                """.formatted(ANSWER)));
        // And a line the declarations do leave values at, that no row arriving at the comparison
        // holds one of: the guard above it has already refused them.
        out.put(UndividedPosition.Reason.NOTHING_ARRIVES_AT_THE_RULES_LINE, of("""
                module m
                %s
                behavior f : (n: Int) -> Answer
                let f (n) = {
                    guard n > 100 else No
                    guard n > 10 else No
                    Yes
                }
                """.formatted(ANSWER)));
        return out;
    }

    /**
     * A word with no model here is a word this test is asking about, and the compiler is what says
     * which words there are.
     *
     * <p>Read off the enumeration rather than from a list written beside it, so that the question
     * arrives with the word rather than the next time somebody thinks to look.
     */
    @Test
    void everyReasonADocumentMayWriteHasAModel() {
        assertEquals(EnumSet.allOf(UndividedPosition.Reason.class), witnesses().keySet(),
                "a word this compiler publishes is one some model reaches");
    }

    /** And each of those models writes its own word into the document a compilation of it makes. */
    @Test
    void eachModelWritesItsWordIntoTheDocument() {
        Map<String, Set<String>> missed = new TreeMap<>();
        witnesses().forEach((reason, witness) -> {
            Set<String> written = wordsWritten(witness);
            if (!written.contains(AdequacyReport.word(reason))) {
                missed.put(AdequacyReport.word(reason), written);
            }
        });
        assertEquals(Map.of(), missed,
                "each word beside what its model's document wrote instead");
    }

    /**
     * And the two words an allowance reaches are two an allowance is what reaches.
     *
     * <p>The other half of {@link #spending}, and the half a sentence cannot hold. Those two models
     * are here because the state is out of reach of what a compilation says, and read under what a
     * compilation says they must write neither word — otherwise the allowance is not what put the
     * word there, the table's account of why they are different from the rest is wrong, and the
     * word would go on being reported as one only a said-down run reaches.
     *
     * <p>Which models these are is read off the table rather than named again. Named, a witness
     * moved onto an allowance would be one this stopped checking with nothing said.
     */
    @Test
    void neitherCostlyWordIsWrittenAtWhatACompilationAllows() {
        Map<String, Set<String>> reached = new TreeMap<>();
        witnesses().forEach((reason, witness) -> {
            if (witness.allowance() instanceof Allowance.AsACompilationDoes) {
                return;
            }
            Set<String> written = wordsWritten(of(witness.source()));
            if (written.contains(AdequacyReport.word(reason))) {
                reached.put(AdequacyReport.word(reason), written);
            }
        });
        assertEquals(Map.of(), reached,
                "a word said to need an allowance said down, beside what its model wrote without"
                        + " one");
    }

    /** The reasons a document of this model publishes, in either field that carries them. */
    private static Set<String> wordsWritten(Witness witness) {
        Compilation compilation = Compilation.ofSource(witness.source(), "Main");
        compilation = switch (witness.allowance()) {
            case Allowance.AsACompilationDoes _ -> compilation;
            case Allowance.ToMeasureWith(PatternPlan.Budget distinctions) ->
                    compilation.withAdequacyPolicy(new AdequacyPolicy(
                            new AdequacyPolicy.OfTheMeasures(Budgets.measures().pairSpace(),
                                    Budgets.measures().cellsPerGroup(), distinctions,
                                    Budgets.measures().rewriteRuns()),
                            Budgets.generation()));
            case Allowance.ToReadWith(ReadingPolicy reading) ->
                    compilation.withReadingPolicy(reading);
        };
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Set<String> out = new LinkedHashSet<>();
        collect(JSON.readTree(AdequacyReport.of(compilation).json(SourceRendering.namedByIdentity(compilation.texts()))),
                out);
        return out;
    }

    /**
     * Every {@code notRead} entry's reason and every shortfall cause's {@code unread}, wherever in
     * the document they stand.
     *
     * <p>Walked rather than reached by a path, because what is being asked is whether the word was
     * written at all: a path written out here would be a second statement of where the writer puts
     * the array, and the day the writer moved it this would report every word as unreachable.
     */
    private static void collect(JsonNode node, Set<String> out) {
        if (node.isObject()) {
            for (String name : node.propertyNames()) {
                if (name.equals("notRead")) {
                    node.get(name).forEach(each -> out.add(each.get("reason").asString()));
                }
                // A cause a limit refused carries no reason, and is not one of these.
                if (name.equals("synthesisShortfallCauses")) {
                    node.get(name).forEach(each -> {
                        if (each.has("unread")) {
                            out.add(each.get("unread").asString());
                        }
                    });
                }
                collect(node.get(name), out);
            }
        } else if (node.isArray()) {
            node.forEach(each -> collect(each, out));
        }
    }
}
