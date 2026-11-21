package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.runtime.ConstraintViolation;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the report reads of two numbers a way ties, held to the program run.
 *
 * <p>The truth is the program: each form is a way and a comparison after it, compiled and run on
 * every pair of numbers of a small box, and the answer says whether the way is passed and, if it
 * is, how the comparison comes out. So for each value of a number the program shows whether the
 * way is passed at every other value or at some, and whether the comparison comes out true at
 * every row that gets to it or at some. What the report says is the classes of each number, cut
 * where the compiler read a line, and where it reads the form it is held to this: a class holds
 * no two values the program tells apart. A line the program draws that the report does not is a
 * class holding two values it tells apart, so that is the one direction asked; a line the report
 * draws and the program does not is no wrong class, only a finer one.
 *
 * <p>A form the report does not read is not held to anything, and what a reader says of the rows
 * of a way rests on a list of what bears on them that it can add to and the program cannot: so the
 * forms are asked of the program and not of whoever wrote the reading. A form is added here when
 * a reading of rows is changed; what the program says is what a reading is checked against.
 */
class ATiedWayIsReadAsTheProgramRunSaysTest {

    private static final int TOP = 12;

    /** A way, and a comparison after it, on {@code e} and {@code p}: {@code e} runs from nought
     *  to twelve, {@code p} from one. */
    private static final Map<String, String[]> FORMS = new LinkedHashMap<>();

    static {
        // One for each way the ties come: a coefficient that rounds in twos, a sum with whole
        // steps, and one that rounds in threes.
        FORMS.put("aLineAndTheDoubleOfAnother", new String[] {"e >= p", "e < 2 * p"});
        FORMS.put("aSumHeldBelowAndTheOrder", new String[] {"e + p <= 12", "e < p"});
        FORMS.put("aTripleOfAnother", new String[] {"e >= p", "e < 3 * p"});
        // A quotient rounded to a whole number is two lines, each on the way to the other.
        FORMS.put("aQuotientRoundedDown", new String[] {"e >= 0",
                "Rational.toInt(DOWN, e / p) == 1"});
        FORMS.put("aQuotientRoundedUp", new String[] {"e >= 0",
                "Rational.toInt(UP, e / p) == 2"});
    }

    /** The least {@code e} of the forms that run below nought. */
    private static final int BELOW = -12;

    /** Forms that run {@code e} from {@link #BELOW}: a quotient rounded toward nought, held at a
     *  whole number below nought, which the way's own line does not cut. */
    private static final Map<String, String[]> FORMS_BELOW_NOUGHT = new LinkedHashMap<>();

    static {
        FORMS_BELOW_NOUGHT.put("aQuotientDownAtMinusOne", new String[] {"e >= -100",
                "Rational.toInt(DOWN, e / p) == -1"});
        FORMS_BELOW_NOUGHT.put("aQuotientUpAtMinusTwo", new String[] {"e >= -100",
                "Rational.toInt(UP, e / p) == -2"});
        FORMS_BELOW_NOUGHT.put("aQuotientDownAtNought", new String[] {"e >= -100",
                "Rational.toInt(DOWN, e / p) == 0"});
        FORMS_BELOW_NOUGHT.put("aQuotientUpAtMinusOne", new String[] {"e >= -100",
                "Rational.toInt(UP, e / p) == -1"});
    }

    private static final Pattern CLASS = Pattern.compile(
            "^[^:]+: (-?\\d+) (<=|<) x (<=|<) (-?\\d+)$");

    /** A class with no greatest value, {@code 3 <= x}, and one with no least, {@code x < 3}. */
    private static final Pattern OPEN_ABOVE = Pattern.compile("^[^:]+: (-?\\d+) (<=|<) x$");
    private static final Pattern OPEN_BELOW = Pattern.compile("^[^:]+: x (<=|<) (-?\\d+)$");

    @Test
    void whatTheReportReadsOfTwoTiedNumbersIsWhatTheProgramRunSays() throws Exception {
        heldToTheProgram(FORMS, 0, Set.of());
    }

    /**
     * Where {@code e} runs below nought a quotient's two lines are sums of the two numbers, and a
     * sum cut at two places is a value cut at several: its positions have no classes of their own
     * and are owed a weight each, which the report says. So no class of {@code e} says anything
     * of the quotient, and the report is held to saying the weight.
     */
    @Test
    void whatTheReportReadsOfAQuotientAtAWholeNumberBelowNoughtIsWhatTheProgramRunSays()
            throws Exception {
        heldToTheProgram(FORMS_BELOW_NOUGHT, BELOW,
                Set.of("aQuotientDownAtMinusOne", "aQuotientUpAtMinusTwo"));
    }

    private static void heldToTheProgram(Map<String, String[]> forms, int eLow,
                                         Set<String> weighedForms) throws Exception {
        List<String> names = new ArrayList<>(forms.keySet());
        StringBuilder model = new StringBuilder("module demo\n\n"
                + "data Eaches = Int\n" + (eLow < 0 ? ""
                        : "    invariant value >= " + eLow + " && value <= " + TOP + "\n")
                + "data PackSize = Int\n    invariant value >= 1 && value <= " + TOP + "\n"
                + "data In = { e: Eaches, p: PackSize }\ndata Out = Int\n");
        for (int at = 0; at < names.size(); at++) {
            String[] form = forms.get(names.get(at));
            model.append("\nbehavior b").append(at).append(" : (i: In) -> Out\nlet b").append(at)
                    .append(" (i) = Out { value = if ").append(written(form[0]))
                    .append(" then (if ").append(written(form[1])).append(" then 1 else 2)")
                    .append(" else 3 }\n");
        }
        Compilation compilation = ACompiledModel.measured(model.toString(),
                Adequacy.Asked.fullReport());
        JsonNode report = JsonMapper.builder().build().readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(model.toString()),
                ATiedWayIsReadAsTheProgramRunSaysTest.class.getClassLoader());
        TreeSet<String> read = new TreeSet<>();
        TreeSet<String> weighed = new TreeSet<>();
        Map<String, String> notRead = new LinkedHashMap<>();
        for (int at = 0; at < names.size(); at++) {
            JsonNode behavior = behaviorNamed(report, "b" + at);
            // A value cut at several places has no classes of its positions: what they are owed
            // in their place is a weight, which the report says, so no class is a claim here.
            if (!behavior.get("partition").path("weights").isEmpty()) {
                weighed.add(names.get(at));
                continue;
            }
            if (!isRead(behavior)) {
                notRead.put(names.get(at), behavior.get("partition").get("notRead").toString());
                continue;
            }
            read.add(names.get(at));
            int[][] outcomes = outcomes(loader, at, eLow);
            for (String axis : List.of("i.e", "i.p")) {
                heldToTheProgram(names.get(at), axis, classesOf(behavior, axis), outcomes, eLow);
            }
        }
        // That the report reads a form is what holds it to the program, so each of these is read:
        // a form no longer read is a reading lost, and agreement on none is none. The forms owed
        // a weight are the ones named, so a form that starts to be read, or to be weighed, shows.
        assertEquals(weighedForms, weighed, "forms weighed");
        TreeSet<String> readForms = new TreeSet<>(names);
        readForms.removeAll(weighedForms);
        assertEquals(readForms, read, "forms read; not read: " + notRead);
    }

    /**
     * Two neighbouring values of {@code e} that the program tells apart by a stop before the
     * comparison are not joined by the report. With {@code e + p} held to an {@code Int}, the
     * least {@code p} that makes {@code e < 2 * p} hold is the greatest {@code p} the sum allows
     * at the one {@code e}, and one more than it at the next: a row each way at the first and a
     * stop where the comparison would hold at the second.
     */
    @Test
    void aStopBeforeTheComparisonTellsTwoNeighboursApartAndTheReportDoesNotReadThem()
            throws Exception {
        String model = """
                module demo

                data Eaches = Int
                    invariant value >= 0
                data PackSize = Int
                    invariant value >= 0 && value <= 4611686018427387903
                data In = { e: Eaches, p: PackSize }
                data Out = Int

                behavior b : (i: In) -> Out
                let b (i) = Out { value =
                    if i.e.value + i.p.value >= 0 && i.e.value >= i.p.value
                            && i.e.value < 2 * i.p.value then 1 else 2 }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(model),
                ATiedWayIsReadAsTheProgramRunSaysTest.class.getClassLoader());
        Object behavior = Emitted.behavior(loader, "demo", "b").getConstructor().newInstance();
        long p = 3_074_457_345_618_258_603L;
        assertEquals(1, ranTo(loader, behavior, 6_148_914_691_236_517_204L, p));
        assertEquals(-1, ranTo(loader, behavior, 6_148_914_691_236_517_205L, p));
        Compilation compilation = ACompiledModel.measured(model, Adequacy.Asked.fullReport());
        JsonNode report = JsonMapper.builder().build().readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        assertTrue(!isRead(behaviorNamed(report, "b")), report::toString);
        assertTrue(report.toString().contains("everyRunStops"), "the stop is told");
    }

    /**
     * Behind a gate that adds the two numbers, an order between them is told apart by a stop at
     * values far from the small ones: at {@code p = 2^62} no {@code e} that passes the gate has
     * the comparison come out as it does at {@code p = 1}, and one more than the greatest stops.
     * A report that holds both to one class of {@code p} says what the program does not. Each way
     * the order is written is a behavior of one model: a number a sum may stop at and one twice or
     * three times the other differ in where the run stops, and none is read.
     */
    @Test
    void anOrderBehindASumThatMayStopIsNotReadHoweverItIsWritten() throws Exception {
        List<String> orders = List.of("i.e.value < i.p.value", "i.e.value < 3 * i.p.value",
                "2 * i.p.value >= i.e.value", "i.e.value < i.p.value + 1");
        StringBuilder model = new StringBuilder("""
                module demo

                data Eaches = Int
                    invariant value >= 0
                data PackSize = Int
                    invariant value >= 0
                data In = { e: Eaches, p: PackSize }
                data Out = Int
                """);
        for (int at = 0; at < orders.size(); at++) {
            model.append("\nbehavior b").append(at).append(" : (i: In) -> Out\nlet b").append(at)
                    .append(" (i) = Out { value = if i.e.value + i.p.value >= 0 then (if ")
                    .append(orders.get(at)).append(" then 1 else 2) else 3 }\n");
        }
        Compilation compilation = ACompiledModel.measured(model.toString(),
                Adequacy.Asked.fullReport());
        JsonNode report = JsonMapper.builder().build().readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        List<String> read = new ArrayList<>();
        for (int at = 0; at < orders.size(); at++) {
            JsonNode behavior = behaviorNamed(report, "b" + at);
            if (isRead(behavior) && behavior.get("partition").path("weights").isEmpty()) {
                read.add(orders.get(at));
            }
        }
        assertEquals(List.of(), read);
    }

    /**
     * A divisor that may be nought: the run stops at a {@code p} of nought whatever {@code e} is,
     * and at no other. A report that reads the quotient does not hold nought in one class with a
     * {@code p} the program does not stop at.
     */
    @Test
    void aDivisorThatMayBeNoughtIsNotHeldInOneClassWithADivisorTheRunDoesNotStopAt()
            throws Exception {
        String model = """
                module demo

                data Eaches = Int
                    invariant value >= 0 && value <= 12
                data PackSize = Int
                    invariant value >= 0 && value <= 12
                data In = { e: Eaches, p: PackSize }
                data Out = Int

                behavior b : (i: In) -> Out
                let b (i) = Out { value =
                    if Rational.toInt(UP, i.e.value / i.p.value) >= 2 then 1 else 2 }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(model),
                ATiedWayIsReadAsTheProgramRunSaysTest.class.getClassLoader());
        Object behavior = Emitted.behavior(loader, "demo", "b").getConstructor().newInstance();
        for (int e : new int[] {0, TOP}) {
            assertEquals(-1, ranTo(loader, behavior, e, 0));
            assertTrue(ranTo(loader, behavior, e, 1) > 0);
        }
        Compilation compilation = ACompiledModel.measured(model, Adequacy.Asked.fullReport());
        JsonNode report = JsonMapper.builder().build().readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        JsonNode behaviorReport = behaviorNamed(report, "b");
        // Read, a class holds no two values the run tells apart, and nought stops where one does
        // not. Not read, no class is claimed.
        if (isRead(behaviorReport)) {
            for (int[] each : classesOf(behaviorReport, "i.p")) {
                assertTrue(each[0] > 0 || each[1] < 1, "nought and one are one class of the"
                        + " divisor: " + behaviorReport.get("partition").get("axes"));
            }
        }
        assertFalse(isRead(behaviorReport), () -> behaviorReport.get("partition").toString());
        // The declarations leave each number a run of its own, every one a value, so an input
        // holding the divisor at nought is shown and the stop the program comes to is said.
        String said = AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(said.contains("· may stop a run"), said);
    }

    /**
     * Where the input holds nothing of its values a run is shown to stop at a divisor of nought:
     * the report says it, in the division and at the value the run stops at, and a divisor the
     * way keeps from nought is said to stop no run.
     */
    @Test
    void aDivisionByNoughtIsToldAsAStopWhereTheInputIsShownToHoldOne() throws Exception {
        String stops = reportOf("""
                module demo

                data Out = Int

                behavior b : (e: Int, p: Int) -> Out
                let b (e, p) = Out { value =
                    if Rational.toInt(UP, e / p) >= 2 then 1 else 2 }
                """);
        assertTrue(stops.contains("· may stop a run: comparison"), stops);
        assertFalse(stops.contains("stop not resolved"), stops);
        String keptAway = reportOf("""
                module demo

                data Out = Int

                behavior b : (e: Int, p: Int) -> Out
                let b (e, p) = Out { value =
                    if p >= 1 then (if Rational.toInt(UP, e / p) >= 2 then 1 else 2) else 3 }
                """);
        assertFalse(keptAway.contains("may stop a run"), keptAway);
        assertFalse(keptAway.contains("stop not resolved"), keptAway);
    }

    /**
     * Of two divisions one in the other, a run stops at the first where its divisor is nought,
     * and has not got to the second: the stop is shown at the first, and the second is left
     * unresolved, where the way holds the first's divisor at nought.
     */
    @Test
    void aStopIsShownAtTheFirstOfTwoDivisionsOneInTheOtherAndNotAtTheSecond() {
        String said = reportOf(quotientOfAQuotient("p == 0"));
        assertTrue(said.contains("· may stop a run: comparison"), said);
        assertTrue(said.contains("whether a run stops in division by q is not determined"), said);
        assertFalse(said.contains("whether a run stops in division by p"), said);
    }

    /**
     * The same through the report a user reads: where {@code q} is the greatest {@code Int},
     * {@code q + 1} stops every run that gets to it, and a run stops at the division by
     * {@code p} before it does, so the report says a run stops.
     */
    @Test
    void aStopAtADivisionIsShownInTheReportWhereAnOperationAfterItWouldStopEveryRun() {
        String said = reportOf("""
                module demo

                data Out = Int

                behavior b : (e: Int, p: Int, q: Int) -> Out
                let b (e, p, q) = Out { value =
                    if q >= 9223372036854775807 then
                        (if Rational.toInt(DOWN, (e / p) / (q + 1)) >= 2 then 1 else 2) else 3 }
                """);
        assertTrue(said.contains("· may stop a run: comparison"), said);
    }

    /** {@code (e / p) / q} compared, on the way where {@code way} holds. */
    private static String quotientOfAQuotient(String way) {
        return """
                module demo

                data Out = Int

                behavior b : (e: Int, p: Int, q: Int) -> Out
                let b (e, p, q) = Out { value =
                    if %s then (if Rational.toInt(UP, (e / p) / q) >= 2 then 1 else 2) else 3 }
                """.formatted(way);
    }

    /** A divisor that is a product of two numbers is no form of them, and a run stops where it is
     *  nought: the stop is left unresolved, and no class is claimed beside it. */
    @Test
    void aDivisorThatIsAProductIsNotReadAndItsStopIsLeftUnresolved() {
        String said = reportOf("""
                module demo

                data Small = Int
                    invariant value >= -3 && value <= 3
                data Out = Int

                behavior b : (e: Int, p: Small, q: Small) -> Out
                let b (e, p, q) = Out { value =
                    if Rational.toInt(UP, e / (p.value * q.value)) >= 2 then 1 else 2 }
                """);
        assertTrue(said.contains("· not read: comparison"), said);
        assertTrue(said.contains("stop not resolved"), said);
    }

    /** A record tying the divisor to the other number by {@code tie}, divided by it. */
    private static String aDivisionBehindAClauseTyingTwoFields(String tie) {
        return """
                module demo

                data In = { e: Int, p: Int }
                    invariant eInRange = e >= 1 && e <= 12
                    invariant tied = %s
                data Out = Int

                behavior b : (i: In) -> Out
                let b (i) = Out { value =
                    if Rational.toInt(UP, i.e / i.p) >= 2 then 1 else 2 }
                """.formatted(tie);
    }

    /**
     * A clause tying the divisor to another field of its record leaves it nought where the other
     * is one, and the program stops there: no clause of either field alone says nought is a value
     * of the divisor, and a value of the record holding both is what shows the stop. Every value
     * the clause leaves runs, but the one with nought.
     */
    @Test
    void aStopIsShownWhereAClauseTyingTwoFieldsLeavesTheDivisorNought() throws Exception {
        String model = aDivisionBehindAClauseTyingTwoFields("p == e - 1");
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(model),
                ATiedWayIsReadAsTheProgramRunSaysTest.class.getClassLoader());
        Object behavior = Emitted.behavior(loader, "demo", "b").getConstructor().newInstance();
        for (int e = 1; e <= TOP; e++) {
            assertEquals(e == 1, ranTo(loader, behavior, e, e - 1) == -1, "e = " + e);
        }
        String said = reportOf(model);
        assertTrue(said.contains("· may stop a run: comparison"), said);
    }

    /** Where the clause leaves the divisor the other number, which is never nought, the program
     *  does not stop, and nothing is said to. */
    @Test
    void noStopIsShownWhereAClauseTyingTwoFieldsKeepsTheDivisorAwayFromNought() throws Exception {
        String model = aDivisionBehindAClauseTyingTwoFields("p == e");
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(model),
                ATiedWayIsReadAsTheProgramRunSaysTest.class.getClassLoader());
        Object behavior = Emitted.behavior(loader, "demo", "b").getConstructor().newInstance();
        for (int e = 1; e <= TOP; e++) {
            assertTrue(ranTo(loader, behavior, e, e) > 0, "e = " + e);
        }
        String said = reportOf(model);
        assertFalse(said.contains("may stop a run"), said);
    }

    private static String reportOf(String model) {
        Compilation compilation = ACompiledModel.measured(model, Adequacy.Asked.fullReport());
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** What the program comes to at {@code e} and {@code p}, or -1 where the run stops. */
    private static int ranTo(ClassLoader loader, Object behavior, long e, long p)
            throws Exception {
        Object in = Codecs.decoded(loader, "demo.In", Map.of("e", e, "p", p));
        try {
            return ((Number) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in)))
                    .intValue();
        } catch (ConstraintViolation stopped) {
            return -1;
        }
    }

    /** {@code e} and {@code p} of the form, as the fields of the input. */
    private static String written(String form) {
        return form.replaceAll("\\be\\b", "i.e.value").replaceAll("\\bp\\b", "i.p.value");
    }

    private static JsonNode behaviorNamed(JsonNode report, String name) {
        for (JsonNode each : report.get("modules").get(0).get("behaviors")) {
            if (each.get("name").asString().equals(name)) {
                return each;
            }
        }
        throw new AssertionError("no behavior " + name);
    }

    /** Whether the report says nothing of the behavior but that its numbers are read: no place is
     *  left not read for a reason that is a fact about no rule read to its end, which is that the
     *  rule relates the two, or that a line of it is one no row turns on. */
    private static boolean isRead(JsonNode behavior) {
        for (JsonNode each : behavior.get("partition").get("notRead")) {
            if (!List.of("rule_relating_two_values", "rule_never_turns_on_this_line")
                    .contains(each.get("reason").asString())) {
                return false;
            }
        }
        return !behavior.get("partition").get("axes").isEmpty();
    }

    /** The classes of the axis of {@code place}, each as the whole numbers it holds. */
    private static List<int[]> classesOf(JsonNode behavior, String place) {
        List<int[]> out = new ArrayList<>();
        for (JsonNode axis : behavior.get("partition").get("axes")) {
            if (!axis.get("axis").asString().endsWith("/" + place)) {
                continue;
            }
            for (JsonNode label : axis.get("classes")) {
                Matcher matched = CLASS.matcher(label.asString());
                Matcher above = OPEN_ABOVE.matcher(label.asString());
                Matcher below = OPEN_BELOW.matcher(label.asString());
                if (matched.matches()) {
                    out.add(new int[] {
                            Integer.parseInt(matched.group(1))
                                    + (matched.group(2).equals("<") ? 1 : 0),
                            Integer.parseInt(matched.group(4))
                                    - (matched.group(3).equals("<") ? 1 : 0)});
                } else if (above.matches()) {
                    out.add(new int[] {Integer.parseInt(above.group(1))
                            + (above.group(2).equals("<") ? 1 : 0), Integer.MAX_VALUE});
                } else if (below.matches()) {
                    out.add(new int[] {Integer.MIN_VALUE, Integer.parseInt(below.group(2))
                            - (below.group(1).equals("<") ? 1 : 0)});
                } else {
                    throw new AssertionError("a class this reads: " + label);
                }
            }
        }
        // A place the report draws no axis of is one class.
        return out.isEmpty() ? List.of(new int[] {Integer.MIN_VALUE, Integer.MAX_VALUE}) : out;
    }

    /**
     * What the program does at each pair: 0 where the way is not passed, 1 where it is and the
     * comparison comes out true, 2 where it comes out false, and -1 where the run stops.
     */
    private static int[][] outcomes(ClassLoader loader, int at, int eLow) throws Exception {
        Object behavior = Emitted.behavior(loader, "demo", "b" + at)
                .getConstructor().newInstance();
        int[][] out = new int[TOP - eLow + 1][TOP + 1];
        for (int e = eLow; e <= TOP; e++) {
            for (int p = 1; p <= TOP; p++) {
                Object in = Codecs.decoded(loader, "demo.In", Map.of("e", (long) e, "p", (long) p));
                try {
                    Object answer = Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
                    out[e - eLow][p] = switch (((Number) answer).intValue()) {
                        case 3 -> 0;
                        default -> ((Number) answer).intValue();
                    };
                } catch (ConstraintViolation stopped) {
                    out[e - eLow][p] = -1;
                }
            }
        }
        return out;
    }

    /**
     * Each value of {@code place}: whether the way is passed at some of the other number's values
     * and at all of them (bit 1 and bit 2), and how the comparison comes out at the rows that get
     * to it (bit 1 true, bit 2 false; none where no row gets there).
     */
    private static void heldToTheProgram(String form, String place, List<int[]> classes,
                                         int[][] outcomes, int eLow) {
        boolean ofE = place.equals("i.e");
        int low = ofE ? eLow : 1;
        int[] way = new int[TOP - low + 1];
        int[] comparison = new int[TOP - low + 1];
        for (int value = low; value <= TOP; value++) {
            for (int other = ofE ? 1 : eLow; other <= TOP; other++) {
                int outcome = ofE ? outcomes[value - eLow][other] : outcomes[other - eLow][value];
                assertTrue(outcome >= 0, form + ": a run stops at " + value + ", " + other);
                way[value - low] |= outcome == 0 ? 2 : 1;
                comparison[value - low] |= outcome == 1 ? 1 : outcome == 2 ? 2 : 0;
            }
        }
        // A class holds no two values the program tells apart: the way is passed alike at them,
        // and the comparison comes out alike at the rows that get to it where both have some.
        for (int[] each : classes) {
            for (int a = Math.max(each[0], low); a <= Math.min(each[1], TOP); a++) {
                for (int b = a + 1; b <= Math.min(each[1], TOP); b++) {
                    assertEquals(way[a - low], way[b - low], form + " " + place + ": " + a
                            + " and " + b + " are in one class, and the way is passed differently");
                    assertTrue(comparison[a - low] == 0 || comparison[b - low] == 0
                                    || comparison[a - low] == comparison[b - low],
                            form + " " + place + ": " + a + " and " + b + " are in one class, "
                                    + "and the comparison comes out differently");
                }
            }
        }
    }
}
