package souther.compiler.query;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.check.ReadingPolicy;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.meta.ModulePath;
import souther.compiler.partition.AdequacyPolicy;
import souther.compiler.partition.Budgets;
import souther.compiler.partition.UndividedPosition;
import souther.compiler.regex.PatternPlan;
import souther.compiler.report.AdequacyReport;
import souther.compiler.values.AsACompilationAllows;

import java.util.EnumMap;
import java.util.EnumSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every word a document writes for a rule it did not read is one a compilation of this compiler
 * puts there.
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
 * <p><b>Total over the vocabulary, by the machine and not by a list beside it.</b> A word added to
 * {@link UndividedPosition.Reason} arrives here as a word with no model, which is the question
 * being asked of whoever added it. There is no arm for a word nobody can reach: a reason nothing
 * produces is one to take out of the vocabulary or to give a way in, and an entry saying so would
 * make this test agree that a promise need not be kept.
 *
 * <p><b>A model here need not compile without a diagnostic.</b> What is claimed is that a
 * compilation writes the word, and this compiler writes an adequacy document about a model it has
 * something to say against — a declaration nothing can construct and a module whose own values are
 * not well founded are both models about which the reading falls short, and the words for falling
 * short are what they are here to reach.
 */
class EveryWordForAnUnreadRuleIsOneSomeCompilationWritesTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * A model, and what a compilation of it may spend.
     *
     * @param sources     the modules handed over, in order
     * @param distinctions what a measure may spend working out what a behavior's rules tell apart,
     *                     or null for what a compilation allows
     * @param reading      what a reading may build with, or null for the same
     */
    private record Witness(List<String> sources, PatternPlan.Budget distinctions,
                           ReadingPolicy reading) {

        Witness {
            sources = List.copyOf(sources);
        }
    }

    private static Witness of(String source) {
        return new Witness(List.of(source), null, null);
    }

    private static Witness across(String... sources) {
        return new Witness(List.of(sources), null, null);
    }

    /**
     * A model read under an allowance said down, which is how the two words for something costing
     * more than this compiler spends are reached.
     *
     * <p>Not a larger model. Every default is set with room over anything anybody would write here,
     * so a model built to exhaust one would be built against the figure rather than against what
     * the word says — and what a compilation may spend is the compilation's to say, which is what
     * these two ask of it.
     */
    private static Witness spending(String source, PatternPlan.Budget distinctions) {
        return new Witness(List.of(source), distinctions, null);
    }

    /** The same, where what is said down is what a reading of the declarations may build with. */
    private static Witness readingWith(String source, ReadingPolicy reading) {
        return new Witness(List.of(source), null, reading);
    }

    /** Room to answer what a position admits, and none to hand each of its rules on as the set it
     *  leaves — which is the second of the two shortfalls one word covers. */
    private static final ReadingPolicy NOTHING_TO_HAND_ON_WITH = new ReadingPolicy(
            ReadAs.THE_COMPILATION_DOES.dnfExpansionLimit(),
            ReadAs.THE_COMPILATION_DOES.scalePlacesLimit(),
            AsACompilationAllows.admittedValues(),
            new PatternPlan.Budget(1, 1));

    /** Deeper than the pattern reader goes, which is what the word is about. */
    private static String nested(int depth) {
        return "(".repeat(depth) + "a" + ")".repeat(depth);
    }

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
                """.formatted(ANSWER), new PatternPlan.Budget(1, 1)));
        // A pattern bracketed deeper than the reader descends, written in a body so that the rule
        // is one the measure was reading rather than a question a declaration left standing.
        out.put(UndividedPosition.Reason.PATTERN_TOO_DEEPLY_NESTED, of("""
                module m
                %s
                behavior f : (code: String) -> Answer
                let f (code) = if String.matches("%s", code) then Yes else No
                """.formatted(ANSWER, nested(220))));
        // Values no line can be drawn on: two booleans are equal or they are not, and neither is
        // above the other.
        out.put(UndividedPosition.Reason.UNSUPPORTED_DOMAIN, of("""
                module m
                %s
                behavior f : (a: Bool, b: Bool) -> Answer
                let f (a, b) = if a == b then Yes else No
                """.formatted(ANSWER)));
        // A string is the one thing two numbers can be taken of — its own order and its length —
        // and a declaration placing an end on each leaves neither able to be the one the position
        // is measured at.
        out.put(UndividedPosition.Reason.COMPETING_COORDINATES, of("""
                module m
                %s
                data Parcel = { label: String }
                    invariant lower = label >= "m"
                    invariant long = String.length(label) >= 3

                behavior f : (parcel: Parcel) -> Answer
                let f (parcel) = Yes
                """.formatted(ANSWER)));
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
        // Values held inside something the walk does not reach into.
        out.put(UndividedPosition.Reason.UNSUPPORTED_TRAVERSAL, of("""
                module m

                data Ok
                data Box = { m: Map<String, Int> }

                behavior f : (b: Box) -> Ok
                let f (b) = Ok
                """));
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
     * And the models between them reach every word, which is the same claim read the other way.
     *
     * <p>Here because the two are not one. A model may write its own word and another's, and what a
     * reader of the vocabulary wants to know is that no word of it is one nothing writes — so the
     * union is asked of the whole table rather than inferred from the entries passing one at a
     * time.
     */
    @Test
    void betweenThemTheModelsWriteEveryWord() {
        Set<String> written = new LinkedHashSet<>();
        witnesses().values().forEach(each -> written.addAll(wordsWritten(each)));
        Set<String> published = new LinkedHashSet<>();
        EnumSet.allOf(UndividedPosition.Reason.class)
                .forEach(each -> published.add(AdequacyReport.word(each)));
        assertTrue(written.containsAll(published),
                () -> "no document these models make writes: " + minus(published, written));
    }

    private static Set<String> minus(Set<String> these, Set<String> those) {
        Set<String> out = new LinkedHashSet<>(these);
        out.removeAll(those);
        return out;
    }

    /** The words a document of this model writes for the rules it did not read. */
    private static Set<String> wordsWritten(Witness witness) {
        Compilation compilation = witness.sources().size() == 1
                ? Compilation.ofSource(witness.sources().get(0), "Main")
                : Compilation.ofSources(witness.sources(), ModulePath.EMPTY);
        if (witness.distinctions() != null) {
            compilation = compilation.withAdequacyPolicy(new AdequacyPolicy(
                    new AdequacyPolicy.OfTheMeasures(Budgets.measures().pairSpace(),
                            witness.distinctions()),
                    Budgets.generation()));
        }
        if (witness.reading() != null) {
            compilation = compilation.withReadingPolicy(witness.reading());
        }
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Set<String> out = new LinkedHashSet<>();
        collect(JSON.readTree(AdequacyReport.of(compilation).json(SourceNameResolver.identity())),
                out);
        return out;
    }

    /**
     * Every {@code notRead} entry's reason, wherever in the document it stands.
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
                collect(node.get(name), out);
            }
        } else if (node.isArray()) {
            node.forEach(each -> collect(each, out));
        }
    }
}
