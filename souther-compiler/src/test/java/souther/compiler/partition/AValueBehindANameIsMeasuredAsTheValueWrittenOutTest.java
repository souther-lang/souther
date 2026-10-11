package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;
import souther.compiler.diag.Diagnostic;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A value an author gave a name is measured as the value written out.
 *
 * <p>{@code s == a} under {@code let a = Alice} states what {@code s == Alice} states, and so does
 * {@code same(s, Alice)} where the helper compares its two parameters. Which of those an author
 * wrote is a matter of spelling, and the partition, the line and the points beside it are owed the
 * same either way. A comparison against a number read that way and against a case or a string read
 * the other: the reading of the other side followed names only for a carrier that counts.
 *
 * <p>Held for each kind of carrier a comparison places a value on, and for each way a value comes
 * to stand behind a name: a value the module declares, a value declared as another, a parameter a
 * helper was handed, a newtype built around a name, and the value written on the left. And held the
 * other way as well: a name standing for another position, or for a value the body chooses, is not
 * the value of either side, and is not measured as if it were.
 */
class AValueBehindANameIsMeasuredAsTheValueWrittenOutTest {

    /** What one behavior's comparison was measured as, with the behavior's own name taken off. */
    private record Measured(List<String> axes, List<String> unread, List<String> points) {}

    private static final String CASES = """
            module probe.named

            data Suspect = Alice | Bob | Carol

            let a = Alice
            let b = a
            let either = if List.isEmpty([1]) then Alice else Bob

            let same (x: Suspect, y: Suspect) = x == y
            let pick (t: Suspect) = if t == Bob then Alice else Carol

            behavior written : (s: Suspect) -> Bool
            let written (s) = s == Alice

            behavior named : (s: Suspect) -> Bool
            let named (s) = s == a

            behavior namedAgain : (s: Suspect) -> Bool
            let namedAgain (s) = s == b

            behavior handed : (s: Suspect) -> Bool
            let handed (s) = same(s, Alice)

            behavior turned : (s: Suspect) -> Bool
            let turned (s) = a == s

            behavior settled : (s: Suspect) -> Bool
            let settled (s) = s == either

            behavior another : (s: Suspect, t: Suspect) -> Bool
            let another (s, t) = s == t

            behavior chosen : (s: Suspect, t: Suspect) -> Bool
            let chosen (s, t) = s == pick(t)
            """;

    private static final String TEXTS = """
            module probe.named

            data Code = String

            let a = "x"
            let b = a
            let c = "y"
            let k = Code(c)

            let same (x: String, y: String) = x == y

            behavior written : (s: String) -> Bool
            let written (s) = s == "x"

            behavior named : (s: String) -> Bool
            let named (s) = s == a

            behavior namedAgain : (s: String) -> Bool
            let namedAgain (s) = s == b

            behavior handed : (s: String) -> Bool
            let handed (s) = same(s, "x")

            behavior turned : (s: String) -> Bool
            let turned (s) = a == s

            behavior wrapped : (s: Code) -> Bool
            let wrapped (s) = s == Code("y")

            behavior wrappedNamed : (s: Code) -> Bool
            let wrappedNamed (s) = s == k
            """;

    private static final String NUMBERS = """
            module probe.named

            data Yen = Int

            let a = 5
            let b = a
            let n = 100
            let y = Yen(n)

            let same (x: Int, z: Int) = x == z

            behavior written : (s: Int) -> Bool
            let written (s) = s == 5

            behavior named : (s: Int) -> Bool
            let named (s) = s == a

            behavior namedAgain : (s: Int) -> Bool
            let namedAgain (s) = s == b

            behavior handed : (s: Int) -> Bool
            let handed (s) = same(s, 5)

            behavior turned : (s: Int) -> Bool
            let turned (s) = a == s

            behavior wrapped : (m: Yen) -> Bool
            let wrapped (m) = m < Yen(100)

            behavior wrappedNamed : (m: Yen) -> Bool
            let wrappedNamed (m) = m < y
            """;

    private static final String TABLES = """
            module probe.named

            data Yen = Int
                invariant value >= 0
            data Row = { lo: Yen, g: Int }
            data Table = List<Row>

            let tbl = Table([Row { lo = Yen(0), g = 1 }, Row { lo = Yen(100), g = 2 }])

            behavior written : (m: Yen) -> Row
            let written (m) =
                List.fold((acc, r) -> if r.lo <= m then r else acc, Row { lo = Yen(0), g = 1 },
                    [Row { lo = Yen(0), g = 1 }, Row { lo = Yen(100), g = 2 }])

            behavior wrapped : (m: Yen) -> Row
            let wrapped (m) =
                List.fold((acc, r) -> if r.lo <= m then r else acc, Row { lo = Yen(0), g = 1 },
                    tbl.value)
            """;

    @Test
    void aCaseBehindANameIsTheCase() {
        Map<String, Measured> read = measured(CASES);
        Measured written = read.get("written");
        assertFalse(written.axes().isEmpty(), "the comparison written out is read: " + written);
        for (String spelling : List.of("named", "namedAgain", "handed", "turned")) {
            assertEquals(written, read.get(spelling), spelling);
        }
    }

    @Test
    void aStringBehindANameIsTheString() {
        Map<String, Measured> read = measured(TEXTS);
        Measured written = read.get("written");
        assertFalse(written.axes().isEmpty(), "the comparison written out is read: " + written);
        for (String spelling : List.of("named", "namedAgain", "handed", "turned")) {
            assertEquals(written, read.get(spelling), spelling);
        }
        assertFalse(read.get("wrapped").axes().isEmpty(), "the construction written out is read");
        assertEquals(read.get("wrapped"), read.get("wrappedNamed"),
                "a newtype built around a name is built around the value the name stands for");
    }

    @Test
    void aNumberBehindANameIsTheNumber() {
        Map<String, Measured> read = measured(NUMBERS);
        Measured written = read.get("written");
        assertFalse(written.axes().isEmpty(), "the comparison written out is read: " + written);
        for (String spelling : List.of("named", "namedAgain", "handed", "turned")) {
            assertEquals(written, read.get(spelling), spelling);
        }
        assertFalse(read.get("wrapped").axes().isEmpty(), "the construction written out is read");
        assertEquals(read.get("wrapped"), read.get("wrappedNamed"));
    }

    @Test
    void aTableTheModuleDeclaresIsTheRowsWrittenInIt() {
        Map<String, Measured> read = measured(TABLES);
        Measured written = read.get("written");
        assertFalse(written.axes().isEmpty(), "the fold over rows written out is read: " + written);
        assertEquals(written, read.get("wrapped"),
                "what a newtype the module declares wraps is the rows written in it");
    }

    @Test
    void aNameForAnotherPositionOrAChosenValueIsNoValueWrittenOut() {
        Map<String, Measured> read = measured(CASES);
        assertNotEquals(read.get("written").points(), read.get("another").points(),
                "a second position is not a case of the first: " + read.get("another"));
        assertNotEquals(read.get("written").points(), read.get("chosen").points(),
                "a value the input chooses between two cases is neither of them: "
                        + read.get("chosen"));
    }

    /** The other side of the line is told apart, so the cases above are told apart by where it
     *  falls and not only by whether one was drawn. */
    @Test
    void aValueTheModuleSettlesAsAnotherCaseDrawsItsLineThere() {
        Map<String, Measured> read = measured(CASES);
        assertFalse(read.get("settled").points().isEmpty(), "read: " + read.get("settled"));
        assertNotEquals(read.get("written").points(), read.get("settled").points(),
                "a line at Bob is not the line at Alice: " + read.get("settled"));
    }

    /**
     * The tree that runs settles a fork on a value the module declares as it settles one on the
     * value written out.
     *
     * <p>There a value is a call of its method, and which arm a run can take is read off that tree.
     * Under a rule that keeps {@code Alice} out, the arm comparing against her is dead whether she is
     * written or named; without the rule both arms are reached, which is what says the answer is the
     * rule's and not the spelling's.
     */
    @Test
    void aCaseTheModuleDeclaresSettlesAForkAsTheCaseWrittenOut() {
        Map<String, List<Boolean>> asked = new LinkedHashMap<>();
        for (String spelling : List.of("Alice", "a", "b")) {
            asked.put(spelling, List.of(deadBranch(true, spelling), deadBranch(false, spelling)));
        }
        assertEquals(Map.of("Alice", List.of(true, false), "a", List.of(true, false),
                        "b", List.of(true, false)), asked,
                "the arm the rule rules out is dead however the case it compares against is named");
    }

    private static boolean deadBranch(boolean ruledOut, String against) {
        return Compiler.compileWithWarnings("""
                module probe.named

                data Suspect = Alice | Bob | Carol
                data Who = Suspect
                %s
                let a = Alice
                let b = a

                behavior f : (w: Who) -> Int
                let f (w) = if w.value == %s then 1 else 2
                """.formatted(ruledOut ? "    invariant Bool.not(value == Alice)" : "", against))
                .warnings().stream()
                .map(Diagnostic::code)
                .anyMatch("E1327"::equals);
    }

    /**
     * A value the module defines as a choice is read in the tree its definition is, and not in the
     * body that compares against it.
     *
     * <p>Following the name, a reader is inside the definition: whether an arm there answers a
     * value is the definition's question. Asked of the body instead, the arm is a node the body was
     * never read at.
     */
    @Test
    void aChoiceTheModuleDefinesIsReadWhereItIsDefined() {
        Map<String, Measured> read = measured("""
                module probe.named

                data Suspect = Alice | Bob | Carol

                let either = if List.fold((t, x) -> t + x, 0, [1, 2]) > 2 then Bob else Carol

                behavior f : (s: Suspect) -> Bool
                let f (s) = s == either
                """);
        Measured f = read.get("f");
        assertNotNull(f, "the model under test compiles: " + read);
        assertFalse(f.points().isEmpty() && f.unread().isEmpty(),
                "the comparison is read, to a line or to a reason it drew none: " + f);
    }

    /**
     * A rule of a declaration admits what it admits however the value it names is spelt.
     *
     * <p>Where the rules of a type say which values may stand at a position, a case named through a
     * value the module declares is the case: {@code Bool.not(value == a)} under {@code let a =
     * Alice} keeps out what {@code Bool.not(value == Alice)} keeps out.
     */
    @Test
    void aRuleAdmitsTheCaseItNamesThroughAValue() {
        Map<String, Measured> read = new LinkedHashMap<>();
        for (String against : List.of("Alice", "a", "b")) {
            read.put(against, measured("""
                    module probe.named

                    data Suspect = Alice | Bob | Carol
                    let a = Alice
                    let b = a
                    data Who = Suspect
                        invariant Bool.not(value == %s)

                    behavior f : (w: Who) -> Bool
                    let f (w) = w.value == Bob
                    """.formatted(against)).get("f"));
        }
        assertFalse(read.get("Alice").axes().isEmpty(), "the rule written out is read: " + read);
        assertEquals(read.get("Alice"), read.get("a"));
        assertEquals(read.get("Alice"), read.get("b"));
    }

    /** What each source was measured as, so a module several tests read is compiled once. */
    private static final Map<String, Map<String, Measured>> MEASURED = new HashMap<>();

    /** Every behavior of {@code source}, measured. */
    private static Map<String, Measured> measured(String source) {
        return MEASURED.computeIfAbsent(source,
                AValueBehindANameIsMeasuredAsTheValueWrittenOutTest::measuredAfresh);
    }

    private static Map<String, Measured> measuredAfresh(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage(module)).value();
        Map<String, List<BorderAssessment>> borders =
                Adequacy.boundariesOf(compilation.db(), module);
        assertNotNull(evidence, "the model under test compiles");
        assertNotNull(borders, "the model under test compiles");
        Map<String, Measured> out = new LinkedHashMap<>();
        evidence.forEach((behavior, each) -> {
            String own = behavior + "/";
            List<String> axes = new ArrayList<>();
            each.axes().forEach(axis ->
                    axes.add(axis.path().replace(own, "") + " " + axis.classes()));
            List<String> unread = new ArrayList<>();
            each.notRead().forEach(not -> unread.add(not.reason().toString()));
            List<String> points = new ArrayList<>();
            borders.getOrDefault(behavior, List.of()).forEach(border -> {
                points.add(border.border().cut().toString()
                        .replace("behavior=" + behavior + ", ", "").replace(own, ""));
                border.items().keySet().forEach(point ->
                        points.add(point.toString().replace(own, "")));
            });
            out.put(behavior, new Measured(axes, unread, points));
        });
        return out;
    }
}
