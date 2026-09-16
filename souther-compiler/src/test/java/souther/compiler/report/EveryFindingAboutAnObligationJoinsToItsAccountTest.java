package souther.compiler.report;

import souther.compiler.diag.SourceRendering;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

import souther.compiler.conformance.ConformanceCorpus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;
import tools.jackson.databind.node.ArrayNode;
import tools.jackson.databind.node.ObjectNode;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A finding that names something a row is owed for names it the way its account names it.
 *
 * <p>What a consumer does with a finding is act on the thing it is about, which means finding that
 * thing in the account the numbers are counted in. The words a reader is shown do not do it: two
 * points of one line are shown the same words where what differs is the run beside the line, and two
 * arms are shown the same word at the same place where what differs is the rule a caller handed the
 * fork. So the identity is written, and this holds that it is written wherever the document names
 * such a thing and that it lands on exactly one entry.
 *
 * <p>Asked of the document rather than of the writer. The rule the writer keeps is that a subject
 * carrying an identity says so by its type, which closes the question locally; what that cannot say
 * is that the identity lands anywhere. Here the two ends are compared: every identity the document
 * publishes on a finding, against the array that account publishes.
 *
 * <p><b>And that one word carries one answer.</b> Whether a row is owed is the subject's, and a
 * kind is a coarsening of the subjects — so a document can put a finding that names an obligation
 * and a finding that names none under one word, and a consumer acting on the second has nothing to
 * look up. That is what the second test below refuses. It was false when it was written: the two
 * kinds it would have caught are the ones this class now reaches on purpose.
 */
@Tag("population")
class EveryFindingAboutAnObligationJoinsToItsAccountTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * One helper of this module's own, called twice with two rules the call sites wrote.
     *
     * <p>A fork the caller decides is one arm per rule handed in, so this body owes two arms at the
     * one {@code if} the helper holds. The helper is written here, so both copies keep the positions
     * they were written at: the two arms are the same word at the same place, and the row that goes
     * through both {@code then}s leaves both {@code else}s owed. They are the case the identity was
     * introduced for — what a reader is shown of the two says nothing about which is which.
     *
     * <p>A library helper is not this case. Its copies are stamped with the call that spliced them,
     * so a reader is shown two places, and the model that reaches for one of those tells the two
     * apart without an identity.
     */
    private static final String TWO_RULES_AT_ONE_FORK = """
            module example.decide

            data Person =
                { active: Bool
                , retired: Bool
                }
            data Yes
            data No
            data Verdict = Yes | No

            let decide (p: (Person) -> Bool, x: Person): Verdict =
                if p(x) then Yes else No

            behavior both : (x: Person) -> Verdict
            let both (x) =
                if decide(a -> a.active, x) == Yes then decide(b -> b.retired, x) else No

            example both
                | "both hold" : (Person { active = true, retired = true }) -> Yes
            """;

    /**
     * Two positions of one behavior, dividing into classes that read alike.
     *
     * <p>The corpus reaches no class no row is in, so the join for one would hold over nothing.
     * Both positions are left in the same class, which is the pair a consumer joining on the words
     * would land on twice — the class is spelled {@code No} at each of them.
     */
    private static final String TWO_POSITIONS_ONE_CLASS_NAME = """
            module example.both

            data Yes
            data No
            data Flag = Yes | No
            data Res = { n: Int }

            behavior both : (left: Flag, right: Flag) -> Res
                constructs Res

            let both (left, right) = Res { n = 1 }

            example both
                | "both say yes" : (Yes, Yes) -> Res { n = 1 }
            """;

    /**
     * Two rules through one arm, one of which no row takes.
     *
     * <p>The corpus reaches no rule no row takes, so the join for one would hold over nothing. Both
     * rules go through the one {@code then}, so the arm account says nothing is missing and the
     * decision account says one rule is — which is the pair the two measures were told apart for.
     */
    private static final String TWO_RULES_ONE_ARM = """
            module example.rule

            data Safe
            data Risky
            data Level = Safe | Risky
            data On
            data Off
            data Switch = On | Off
            data Verdict = { n: Int }

            behavior act : (level: Level, power: Switch) -> Verdict
                constructs Verdict

            let act (level, power) =
                if level == Safe then
                    if power == On then Verdict { n = 1 } else Verdict { n = 2 }
                else
                    Verdict { n = 3 }

            example act
                | "safe and on"  : (Safe, On) -> Verdict { n = 1 }
                | "risky"        : (Risky, On) -> Verdict { n = 3 }
            """;

    /**
     * A sum an input ranges over, one case of which no row applies the behavior to.
     *
     * <p>The one obligation two measures reach. The signature counts the cases a row applies the
     * behavior to and the partition counts the classes a row sits in, and for a top-level sum they
     * are the same thing a row is owed for — so the two findings name one entry or the account has
     * the same work in it twice.
     */
    private static final String A_CASE_AND_ITS_CLASS = """
            module example.case

            data Yes
            data No
            data Flag = Yes | No
            data Res = { n: Int }

            behavior only : (flag: Flag) -> Res
                constructs Res

            let only (flag) = Res { n = 1 }

            example only
                | "yes" : (Yes) -> Res { n = 1 }
            """;

    /**
     * A row written {@code <?>} at an arm nothing else covers.
     *
     * <p>Two obligations about one piece of text, and one kind covers both. The arm is owed a row
     * and the row that stands there does not answer, so the arm account holds it; the row is owed
     * an answer and only an answer written where it is discharges that, so the row account holds
     * it. The corpus reaches neither on its own, and a join asked of a kind rather than of the
     * identity lands both findings on whichever account the kind was written down against.
     */
    private static final String A_ROW_AWAITING_ITS_ANSWER = """
            module example.owed

            data Yes
            data No
            data Flag = Yes | No
            data Res = { n: Int }

            behavior decide : (flag: Flag) -> Res
                constructs Res

            let decide (flag) = if flag == Yes then Res { n = 1 } else Res { n = 2 }

            example decide
                | "yes"  : (Yes) -> Res { n = 1 }
                | "no"   : (No) -> <?>
            """;

    /**
     * Every obligation identity the document publishes lands on exactly one entry of its account.
     *
     * <p>The population is the findings that carry an identity, which is what the document writes
     * wherever the subject is one. Taken off a list of kinds instead, the sweep is as wide as
     * whoever last edited the list — and a kind whose findings the account has no entry for is
     * exactly what such a list hides.
     */
    @Test
    void everyObligationIdentityThatIsPublishedJoinsToOneEntryOfItsAccount() {
        List<String> wrong = new ArrayList<>();
        int joined = 0;
        for (JsonNode document : DOCUMENTS) {
            for (JsonNode module : document.get("modules")) {
                for (JsonNode behavior : module.get("behaviors")) {
                    for (JsonNode finding : behavior.get("findings")) {
                        JsonNode id = finding.get("obligationId");
                        if (id == null) {
                            continue;
                        }
                        joined++;
                        String kind = finding.get("kind").asString();
                        long found = entriesOf(behavior, module, kind).stream()
                                .filter(entry -> id.equals(entry.get("obligationId"))).count();
                        if (found != 1) {
                            wrong.add(behavior.get("name").asString() + ": a " + kind
                                    + " finding joins " + found + " entries");
                        }
                    }
                }
            }
        }
        assertEquals(List.of(), wrong, "a published obligation identity joins to its account");
        assertTrue(joined > 0, "and the corpus reaches findings that publish one");
    }

    /**
     * And a finding a build acts on carries the code it is told under.
     *
     * <p>The other half of being able to refuse over something. What a build does about a finding
     * is its subject's answer and which code it is told under is its kind's, and the two used to be
     * held in step by asking one enum both questions. Asked here of the document, where what a
     * build does and what it prints are both written: a finding a build refuses over or holds a
     * verdict open for and no code beside it is a gap a report prints and a build is never told
     * about.
     */
    @Test
    void andAFindingABuildActsOnCarriesItsCode() {
        List<String> wrong = new ArrayList<>();
        int acted = 0;
        for (JsonNode document : DOCUMENTS) {
            for (JsonNode module : document.get("modules")) {
                for (JsonNode behavior : module.get("behaviors")) {
                    for (JsonNode finding : behavior.get("findings")) {
                        if ("reported".equals(finding.get("disposition").asString())) {
                            continue;
                        }
                        acted++;
                        if (!finding.has("code")) {
                            wrong.add(finding.get("kind").asString()
                                    + ": a build acts on this and is told nothing");
                        }
                    }
                }
            }
        }

        assertEquals(List.of(), wrong, "a finding a build acts on has no code to be told under");
        assertTrue(acted > 0, "and the corpus reaches findings a build acts on");
    }

    /**
     * And the findings of one kind agree about whether they name an obligation.
     *
     * <p>The direction that used to be false. Whether a row is owed was answered twice — once per
     * subject, which is what makes the writer publish a key, and once per kind, which is what a
     * build's refusal and the offering read — and a kind is a coarsening of the subjects, so the
     * two could disagree and did: one kind covered a subject that named an obligation and a subject
     * that named nothing, and a consumer acting on the second had nothing to look up while a build
     * refused over it.
     *
     * <p>Asked of the document rather than of the types. That a subject carrying an identity says
     * so by its type closes the question where the finding is made; this says the document that
     * comes out of it does not put two answers under one word, which is the form a consumer meets
     * the defect in.
     */
    @Test
    void andTheFindingsOfOneKindAgreeAboutNamingAnObligation() {
        Map<String, Boolean> named = new LinkedHashMap<>();
        List<String> wrong = new ArrayList<>();
        for (JsonNode document : DOCUMENTS) {
            for (JsonNode module : document.get("modules")) {
                for (JsonNode behavior : module.get("behaviors")) {
                    for (JsonNode finding : behavior.get("findings")) {
                        String kind = finding.get("kind").asString();
                        boolean names = finding.has("obligationId");
                        Boolean said = named.putIfAbsent(kind, names);
                        if (said != null && said != names) {
                            wrong.add(kind + ": one finding of this kind names an obligation and"
                                    + " another names none");
                        }
                    }
                }
            }
        }

        assertEquals(List.of(), wrong, "one kind, two answers about what a row is owed");
        assertTrue(named.containsValue(true) && named.containsValue(false),
                () -> "and the corpus reaches kinds on both sides of it: " + named);
    }

    /**
     * Two arms of one fork, told apart by nothing a reader is shown.
     *
     * <p>The case the identity is for. Both are the {@code else} of one {@code if}, both are written
     * where that {@code if} is, and they are two things to cover because two callers handed the fork
     * two rules. Joined on what a reader is shown, a consumer lands on both or on whichever came
     * first.
     */
    @Test
    void twoArmsATableCannotTellApartAreToldApartByTheirIdentity() {
        JsonNode behavior = onlyBehaviorOf(reportOf(TWO_RULES_AT_ONE_FORK));
        Map<String, List<JsonNode>> shownAlike = new LinkedHashMap<>();
        for (JsonNode finding : behavior.get("findings")) {
            if ("arm_unreached".equals(finding.get("kind").asString())) {
                shownAlike.computeIfAbsent(
                        finding.get("subject").asString() + " " + finding.get("at"),
                        _ -> new ArrayList<>()).add(finding);
            }
        }

        List<JsonNode> together = shownAlike.values().stream()
                .filter(each -> each.size() > 1).findFirst()
                .orElseThrow(() -> new AssertionError(
                        "two arms shown alike: " + behavior.get("findings")));
        assertEquals(2, together.size(),
                () -> "the helper's else, once per rule handed to it: " + together);
        assertEquals(2, together.stream()
                        .map(f -> String.valueOf(f.get("obligationId"))).distinct().count(),
                () -> "told apart by which rule the caller handed the fork: " + together);
        // And each of them is the identity of one entry of the account, which is what the join
        // above holds of every finding — said here of the pair a reader cannot tell apart, since
        // that is the pair a consumer would land on twice.
        for (JsonNode arm : together) {
            assertEquals(1, entriesOf(behavior, onlyModuleOf(reportOf(TWO_RULES_AT_ONE_FORK)),
                            "arm_unreached").stream()
                            .filter(entry -> arm.get("obligationId").equals(
                                    entry.get("obligationId"))).count(),
                    () -> "and lands on one arm of the account: " + arm);
        }
    }

    /**
     * Two classes spelled alike at two positions, each landing on its own axis.
     *
     * <p>Said here as well as in the sweep above because the sweep is over whatever the corpus
     * happens to reach, and it reaches no class no row is in. A join that holds over nothing holds
     * while the mechanism is gone.
     */
    @Test
    void twoClassesSpeltAlikeLandOnTheAxisEachIsAClassOf() {
        JsonNode document = reportOf(TWO_POSITIONS_ONE_CLASS_NAME);
        JsonNode behavior = onlyBehaviorOf(document);
        List<JsonNode> classes = new ArrayList<>();
        for (JsonNode finding : behavior.get("findings")) {
            if ("axis_class_uncovered".equals(finding.get("kind").asString())) {
                classes.add(finding);
            }
        }

        assertEquals(2, classes.size(),
                () -> "one class left at each position: " + behavior.get("findings"));
        assertEquals(1, classes.stream()
                        .map(f -> f.get("obligationId").get("class").asString()).distinct().count(),
                () -> "spelt alike: " + classes);
        assertEquals(2, classes.stream()
                        .map(f -> String.valueOf(f.get("obligationId"))).distinct().count(),
                () -> "told apart by which position's axis: " + classes);
        for (JsonNode each : classes) {
            assertEquals(1, entriesOf(behavior, onlyModuleOf(document), "axis_class_uncovered")
                            .stream()
                            .filter(entry -> each.get("obligationId")
                                    .equals(entry.get("obligationId"))).count(),
                    () -> "and lands on one class of the axes: " + each);
        }
    }

    /**
     * A case of an input and the class of its position are one entry, not two that coincide.
     *
     * <p>The one place two derivations reach one obligation. What the signature counts and what the
     * partition counts are the same thing a row is owed for at a top-level sum, so a consumer
     * acting on both is acting on one item of work — and a verdict counting each of them is
     * counting one gap twice.
     *
     * <p>Said of the identity rather than of the words. Both findings name the case, so a consumer
     * joining on what a reader is shown would land on one entry by coincidence and would go on
     * doing it until two positions of one behavior divided into classes that read alike.
     */
    @Test
    void aCaseOfAnInputAndTheClassOfItsPositionAreOneEntry() {
        JsonNode document = reportOf(A_CASE_AND_ITS_CLASS);
        JsonNode behavior = onlyBehaviorOf(document);
        List<JsonNode> cases = new ArrayList<>();
        List<JsonNode> classes = new ArrayList<>();
        for (JsonNode finding : behavior.get("findings")) {
            String kind = finding.get("kind").asString();
            if ("input_case_unspecified".equals(kind)) {
                cases.add(finding);
            } else if ("axis_class_uncovered".equals(kind)) {
                classes.add(finding);
            }
        }

        assertEquals(1, cases.size(),
                () -> "one case of the input has no row: " + behavior.get("findings"));
        assertEquals(1, classes.size(),
                () -> "and the position divides into one class no row is in: "
                        + behavior.get("findings"));
        assertEquals(classes.get(0).get("obligationId"), cases.get(0).get("obligationId"),
                () -> "the two measures reached one obligation: " + cases + " / " + classes);
        assertEquals(1, entriesOf(behavior, onlyModuleOf(document), "axis_class_uncovered").stream()
                        .filter(entry -> cases.get(0).get("obligationId")
                                .equals(entry.get("obligationId"))).count(),
                () -> "which the account holds once: " + behavior.get("partition"));
    }

    /**
     * A row awaiting its answer and the arm it stands at are two entries of two accounts.
     *
     * <p>One kind and two obligations, which is why the join is asked of the identity. Both
     * findings are {@code unanswered_row}; one is keyed on the arm and lands in the arm account,
     * the other on the row and lands in the row account. A reader taking the account from the kind
     * puts both against whichever of the two was written down, and the one it was not written down
     * against joins nothing.
     */
    @Test
    void aRowAwaitingItsAnswerAndTheArmItStandsAtAreTwoEntries() {
        JsonNode document = reportOf(A_ROW_AWAITING_ITS_ANSWER);
        JsonNode behavior = onlyBehaviorOf(document);
        List<JsonNode> owed = new ArrayList<>();
        for (JsonNode finding : behavior.get("findings")) {
            if ("unanswered_row".equals(finding.get("kind").asString())) {
                owed.add(finding);
            }
        }

        assertEquals(2, owed.size(),
                () -> "the arm is owed a row and the row is owed an answer: "
                        + behavior.get("findings"));
        assertEquals(2, owed.stream()
                        .map(each -> String.valueOf(each.get("obligationId"))).distinct().count(),
                () -> "told apart by what each is owed at: " + owed);
        for (JsonNode each : owed) {
            assertEquals(1, entriesOf(behavior, onlyModuleOf(document), "unanswered_row").stream()
                            .filter(entry -> each.get("obligationId")
                                    .equals(entry.get("obligationId"))).count(),
                    () -> "and each lands on one entry of the account it is owed at: " + each);
        }
        List<String> stands = new ArrayList<>();
        behavior.get("rowObligations")
                .forEach(each -> stands.add(each.get("disposition").asString()));
        assertEquals(List.of("met", "unmet"), stands,
                () -> "and the account holds both rows, not only the one a finding is about: "
                        + behavior.get("rowObligations"));
    }

    private static List<JsonNode> entriesOf(JsonNode behavior, JsonNode module, String kind) {
        List<JsonNode> out = new ArrayList<>();
        // A combination of two classes, where the body's decisions meet nowhere and the pair space
        // is what the behavior is held to. Made here for the reason a class of a position is: the
        // axes carry every class of every position and the pairs carry which two positions each
        // relation is between, so a cell is those two read together and an array beside them would
        // be the same membership declared twice.
        if ("pair_uncovered".equals(kind)) {
            return pairCellsOf(behavior);
        }
        // The combinations of the body's own decisions, which the account publishes one entry of
        // per combination the body has a path to.
        if ("interaction_uncovered".equals(kind)) {
            behavior.get("interaction").get("obligations").forEach(out::add);
            return out;
        }
        // A class of a position is kept as the axis it is a class of and the string that axis
        // lists, so the entry a finding joins to is that pair. Made here rather than published as
        // a third array, because the axes already carry every class of every position and an array
        // beside them would be the same membership declared twice.
        if ("axis_class_uncovered".equals(kind)) {
            for (JsonNode axis : behavior.get("partition").get("axes")) {
                for (JsonNode cls : axis.get("classes")) {
                    ObjectNode entry = JSON.createObjectNode();
                    ObjectNode id = entry.putObject("obligationId");
                    id.put("axis", axis.get("axis").asString());
                    id.put("class", cls.asString());
                    out.add(entry);
                }
            }
            return out;
        }
        // A case of an input is owed at one of two entries, and which is not this reader's to
        // decide: where the behavior has a position of its own the case and the class its position
        // divides into are one thing a row is owed for and the axes publish it; where it has none
        // the signature publishes the case itself. So both are in hand and the identity on the
        // finding says which it lands on.
        if ("input_case_unspecified".equals(kind)) {
            out.addAll(entriesOf(behavior, module, "axis_class_uncovered"));
            if (behavior.has("signature")) {
                for (JsonNode input : behavior.get("signature").get("inputs")) {
                    input.get("obligations").forEach(out::add);
                }
            }
            return out;
        }
        // A row waiting for its answer is owed at one of two entries, and which is not this
        // reader's to decide. The arm such a row stands at is owed a row and the arm account holds
        // that; the row itself is owed an answer and the row account holds that — two obligations
        // about one piece of text, and the identity on the finding says which it is about.
        if ("unanswered_row".equals(kind)) {
            // A behavior with no arms has no arm account to publish, and a row of one is waiting
            // for its answer all the same.
            JsonNode arms = behavior.get("branch").get("obligations");
            if (arms != null) {
                arms.forEach(out::add);
            }
            behavior.get("rowObligations").forEach(out::add);
            return out;
        }
        JsonNode from = switch (kind) {
            case "decision_rule_uncovered" -> behavior.get("decision").get("obligations");
            // A case of the output, whose account is under the output itself. No second place to
            // look: an axis is of an input, so nothing else has an entry this could land on.
            case "output_case_unspecified" ->
                    behavior.get("signature").get("output").get("obligations");
            case "arm_unreached" -> behavior.get("branch").get("obligations");
            case "boundary_unmet", "domain_point_uncovered" ->
                    behavior.get("partition").get("obligations");
            default -> throw new IllegalStateException(kind);
        };
        from.forEach(out::add);
        // A line a declaration drew is owed once for the module and is kept under the declaration,
        // so a finding about one joins there rather than in the behavior it was read at.
        for (JsonNode declared : module.get("declarations")) {
            declared.get("obligations").forEach(out::add);
        }
        return out;
    }

    /**
     * Every combination of two classes the pair space holds, as this document has them.
     *
     * <p>Which two positions each relation is between is under {@code pairs}, and what each of them
     * divides into is under {@code axes}: a cell is one class of the one and one class of the
     * other. Written in the order the identity is written in, since the two classes are a set and a
     * consumer joining on them reads whatever order the document spelled.
     */
    private static List<JsonNode> pairCellsOf(JsonNode behavior) {
        JsonNode partition = behavior.get("partition");
        Map<String, List<String>> classesOf = new LinkedHashMap<>();
        for (JsonNode axis : partition.get("axes")) {
            List<String> classes = new ArrayList<>();
            axis.get("classes").forEach(each -> classes.add(each.asString()));
            classesOf.put(axis.get("axis").asString(), classes);
        }
        List<JsonNode> out = new ArrayList<>();
        for (JsonNode pair : partition.get("pairs").get("between")) {
            String one = pair.get("one").asString();
            String other = pair.get("other").asString();
            for (String first : classesOf.getOrDefault(one, List.of())) {
                for (String second : classesOf.getOrDefault(other, List.of())) {
                    ObjectNode entry = JSON.createObjectNode();
                    ObjectNode id = entry.putObject("obligationId");
                    id.put("behavior", behavior.get("name").asString());
                    List<List<String>> both = new ArrayList<>();
                    both.add(List.of(one, first));
                    both.add(List.of(other, second));
                    both.sort(Comparator.<List<String>, String>comparing(each -> each.get(0))
                            .thenComparing(each -> each.get(1)));
                    ArrayNode of = id.putArray("classes");
                    for (List<String> each : both) {
                        ObjectNode at = of.addObject();
                        at.put("axis", each.get(0));
                        at.put("class", each.get(1));
                    }
                    out.add(entry);
                }
            }
        }
        return out;
    }

    private static JsonNode onlyBehaviorOf(JsonNode document) {
        return onlyModuleOf(document).get("behaviors").get(0);
    }

    private static JsonNode onlyModuleOf(JsonNode document) {
        return document.get("modules").get(0);
    }

    private static JsonNode reportOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return JSON.readTree(
                AdequacyReport.of(compilation).json(SourceRendering.namedByIdentity(compilation.texts())));
    }

    /**
     * The documents both sweeps read, written once for the class that asks.
     *
     * <p>Both questions are about the same models and the compiling is nearly all of what they
     * cost. Asked per question, the corpus would be analysed again for each.
     */
    private static final List<JsonNode> DOCUMENTS = documents();

    private static List<JsonNode> documents() {
        List<JsonNode> out = new ArrayList<>();
        for (ConformanceCorpus corpus : ConformanceCorpus.all()) {
            ConformanceCorpus.Analysed analysed = corpus.analyse();
            out.add(JSON.readTree(analysed.report().json(
                    new SourceRendering(corpus.names(), analysed.compilation().texts()))));
        }
        out.add(reportOf(TWO_RULES_AT_ONE_FORK));
        out.add(reportOf(TWO_POSITIONS_ONE_CLASS_NAME));
        out.add(reportOf(TWO_RULES_ONE_ARM));
        out.add(reportOf(A_CASE_AND_ITS_CLASS));
        out.add(reportOf(A_ROW_AWAITING_ITS_ANSWER));
        return out;
    }
}
