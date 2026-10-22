package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A list a flattening puts together of a list of one value or of none for each element is the
 * elements it answers one for, each once, as the value it answered: a map of the elements some
 * statement keeps. Three things are read of it apart, and none is assumed of another.
 *
 * <p>How many it holds is how many elements take an arm answering one, added up over them as a
 * number chosen by the arms of each ({@code Pullback#sizedByTheArmsOfAnElement}). Which elements
 * those are is what that count counts, read as the statement any operation keeping some elements
 * is read by. What each holds is read off the value the arm wrote, as a map's answer is. And what
 * a fold files of the elements a statement keeps is filed of those alone: the end of each key is
 * the end among the kept elements of that key.
 */
class AListOfOneValueOrNoneForEachElementIsReadAsTheElementsItKeepsTest {

    private static final String HEAD = """
            module probe.kept

            data Num = { key: String, n: Int }
            data WithKey = { key: String, n: Int }
            data WithoutKey = { n: Int }
            data Kind = WithKey | WithoutKey
            data Box = { items: List<Int>, open: Bool }
            data Report = { stale: List<String> }

            let keysOf (k: Kind): List<(String, Int)> =
                match k with
                    | WithKey { key, n } -> [ (key, n) ]
                    | WithoutKey -> []

            let keyOf (k: Kind): List<String> =
                match k with
                    | WithKey { key } -> [ key ]
                    | WithoutKey -> []

            let nOf (k: Kind): Int =
                match k with
                    | WithKey { n } -> n
                    | WithoutKey { n } -> n

            let pairsOf (k: Kind): List<(String, Int)> = List.map(key -> (key, nOf(k)), keyOf(k))

            data ToAccount = { accountId: String }
            data ToDeal = { accountId: String, deal: String }
            data ToLead = { lead: String }
            data Related = ToAccount | ToDeal | ToLead
            data Act = { related: Related, on: Int }

            let accountOf (a: Act): List<String> =
                match a.related with
                    | ToAccount { accountId } -> [ accountId ]
                    | ToDeal { accountId } -> [ accountId ]
                    | ToLead -> []

            let datesOf (a: Act): List<(String, Int)> = List.map(k -> (k, a.on), accountOf(a))

            """;

    private static List<String> notRead(String behavior) {
        Compilation compilation = Compilation.ofSource(HEAD + behavior, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
        List<String> said = new ArrayList<>();
        for (AdequacyReport.BehaviorReport each :
                AdequacyReport.of(compilation).modules().get(0).behaviors()) {
            each.partition().notRead().forEach(one -> said.add(one.at() + " " + one.reason()));
        }
        return said.stream().sorted().toList();
    }

    /** A fold filing how often each key occurs among {@code pairs}, built as {@code built}. */
    private static String countedOver(String parameters, String built) {
        return """
                behavior f : (%s) -> Report
                let f (%s) = {
                    let pairs: List<(String, Int)> = %s
                    let since: Map<String, Int> = List.fold((acc, pair) -> {
                        let (key, n) = pair
                        Map.updateOrInsert(key, 1, seen -> seen + 1, acc)
                    }, Map.empty, pairs)
                    Report { stale = Map.keys(Map.filterEntries((k, v) -> v >= 2, since)) }
                }
                """.formatted(parameters, parameters.replaceAll(": [^,]*", ""), built);
    }

    /** A fold filing the least {@code n} of each key among {@code pairs}, built as {@code built}. */
    private static String leastOver(String parameters, String built) {
        return """
                behavior f : (%s) -> Report
                let f (%s) = {
                    let pairs: List<(String, Int)> = %s
                    let since: Map<String, Int> = List.fold((acc, pair) -> {
                        let (key, n) = pair
                        Map.updateOrInsert(key, n, seen -> Int.min(seen, n), acc)
                    }, Map.empty, pairs)
                    Report { stale = Map.keys(Map.filterEntries((k, v) -> v >= 30, since)) }
                }
                """.formatted(parameters, parameters.replaceAll(": [^,]*", ""), built);
    }

    /**
     * Each element taking an arm that answers one value adds one, and one taking an arm answering
     * none adds none, so how many the flattening holds is how many take the first: read whole. An
     * arm answering as many as a list of the element holds adds a number of its own on top of
     * being taken, which no form holds.
     */
    @Test
    void howManyAFlatteningHoldsIsHowManyElementsTakeAnArmAnsweringOne() {
        assertEquals(List.of(), notRead("""
                behavior f : (kinds: List<Kind>) -> Bool
                let f (kinds) = List.length(List.flatMap(k -> keysOf(k), kinds)) >= 2
                """));
        assertEquals(List.of(), notRead("""
                behavior f : (kinds: List<Kind>) -> Bool
                let f (kinds) = List.length(List.flatMap(k -> match k with
                    | WithKey { key } -> [ key, key ]
                    | WithoutKey -> [], kinds)) >= 3
                """));
        assertEquals(List.of("boxes RULE_ABOUT_A_DERIVED_VALUE",
                        "boxes[*].items RULE_ABOUT_A_DERIVED_VALUE",
                        "boxes[*].open RULE_ABOUT_A_DERIVED_VALUE"),
                notRead("""
                        behavior f : (boxes: List<Box>) -> Bool
                        let f (boxes) = List.length(List.flatMap(
                            b -> if b.open then b.items else [], boxes)) >= 2
                        """));
    }

    /** One value for every element is the map of the elements to it, read as the map is. */
    @Test
    void aFlatteningOfOneValueForEachElementIsTheMapOfIt() {
        List<String> mapped = notRead(leastOver("nums: List<Num>",
                "List.map(a -> (a.key, a.n), nums)"));
        assertEquals(List.of("least(nums[*].n by key) RULE_ABOUT_A_RUN"), mapped);
        assertEquals(mapped, notRead(leastOver("nums: List<Num>",
                "List.flatMap(a -> [(a.key, a.n)], nums)")));
        assertEquals(List.of("occurrences(kinds[*]@WithKey.key kept by kinds meeting kinds[*] is"
                        + " WithKey) RULE_ABOUT_A_RUN"),
                notRead(countedOver("kinds: List<Kind>", "List.flatMap(k -> keysOf(k), kinds)")));
    }

    /**
     * One value for some elements and none for others keeps the elements answering one, and a
     * count of a key among them counts those alone, by the statement the flattening's size reads:
     * whether it is written in the closure or in a map over a list of one or none, which is the
     * same list.
     */
    @Test
    void aFlatteningOfOneValueOrNoneKeepsTheElementsAnArmAnswersOneFor() {
        List<String> counted = notRead(countedOver("kinds: List<Kind>",
                "List.flatMap(k -> keysOf(k), kinds)"));
        assertEquals(List.of("occurrences(kinds[*]@WithKey.key kept by kinds meeting kinds[*] is"
                + " WithKey) RULE_ABOUT_A_RUN"), counted);
        assertEquals(counted, notRead(countedOver("kinds: List<Kind>",
                "List.flatMap(k -> pairsOf(k), kinds)")));
        // And what a fold files of each is read off the element it was made of, as the case the
        // arm took: the end of each key is the end among the elements of that case.
        List<String> least = notRead(leastOver("kinds: List<Kind>",
                "List.flatMap(k -> keysOf(k), kinds)"));
        assertEquals(List.of("least(kinds[*]@WithKey.n kept by kinds meeting kinds[*] is WithKey"
                + " by key) RULE_ABOUT_A_RUN"), least);
        assertEquals(least, notRead(leastOver("kinds: List<Kind>",
                "List.flatMap(k -> pairsOf(k), kinds)")));
    }

    /**
     * Arms answering a value, each chosen by a case of one place of the element, make each
     * element by the arm its case is taken by: the key is what that arm reads, at the place its
     * case has it, and the elements kept are those taking either arm. Written in a helper or in
     * the closure, it is the same list.
     */
    @Test
    void aKeyEachCaseHoldsAtItsOwnPlaceIsReadAtThePlaceOfTheElementsCase() {
        List<String> least = notRead(leastOver("acts: List<Act>",
                "List.flatMap(a -> datesOf(a), acts)"));
        assertEquals(List.of("least(acts[*].on kept by acts meeting any[acts[*].related is"
                + " ToAccount, acts[*].related is ToDeal] by when related@ToAccount then"
                + " related@ToAccount.accountId when related@ToDeal then"
                + " related@ToDeal.accountId) RULE_ABOUT_A_RUN"), least);
        assertEquals(least, notRead(leastOver("acts: List<Act>", """
                List.flatMap(a -> match a.related with
                    | ToAccount { accountId } -> [ (accountId, a.on) ]
                    | ToDeal { accountId } -> [ (accountId, a.on) ]
                    | ToLead -> [], acts)""")));
        // What each element comes to is chosen by the same case as its key.
        assertEquals(List.of("least({when related@ToAccount then 1·on + 0 when"
                + " related@ToDeal then 1·on + 1 | acts[*]} kept by acts meeting"
                + " any[acts[*].related is ToAccount, acts[*].related is ToDeal] by when"
                + " related@ToAccount then related@ToAccount.accountId when related@ToDeal then"
                + " related@ToDeal.accountId) RULE_ABOUT_A_RUN"),
                notRead(leastOver("acts: List<Act>", """
                        List.flatMap(a -> match a.related with
                            | ToAccount { accountId } -> [ (accountId, a.on) ]
                            | ToDeal { accountId } -> [ (accountId, a.on + 1) ]
                            | ToLead -> [], acts)""")));
    }

    /** A key chosen by case is written with each arm's case and way, in a document the schema
     *  shipped beside this accepts. */
    @Test
    void aKeyChosenByCaseIsWrittenInADocumentTheSchemaAccepts() {
        Compilation compilation = Compilation.ofSource(HEAD + leastOver("acts: List<Act>",
                "List.flatMap(a -> datesOf(a), acts)"), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String json = AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
        JsonNode written = JsonMapper.builder().build().readTree(json);
        DocumentShape.assertShapedLikeTheSchema(written);
        List<JsonNode> byCase = new ArrayList<>();
        written.findParents("key_by_case").forEach(each -> byCase.add(each.get("key_by_case")));
        assertEquals(List.of("acts[*].related@ToAccount[sum-case]"
                                + " acts[*].related@ToAccount[sum-case].accountId",
                        "acts[*].related@ToDeal[sum-case]"
                                + " acts[*].related@ToDeal[sum-case].accountId"),
                byCase.getFirst().get("arms").valueStream().map(arm -> arm.get("taken")
                        .asString() + " " + arm.get("key").asString()).toList(), json);
    }

    /** Two arms answering a value are two values an element may be made into, and what a fold
     *  files of them is of neither alone. */
    @Test
    void anEndOfWhatTwoArmsAnswerIsNotReadAsTheEndOfEither() {
        assertEquals(List.of("nums[*] RULE_ABOUT_A_DERIVED_VALUE"), notRead(leastOver(
                "nums: List<Num>", """
                        List.flatMap(a -> if a.n > 3 then [ (a.key, a.n) ]
                                          else [ (a.key, 0 - a.n) ], nums)""")));
    }

    /**
     * What is taken out of what the arms answer comes to one place only where every arm answering
     * a value takes it from the same place; arms answering two values, or one taken out of
     * different places, are no list of one value or none of the element's.
     */
    @Test
    void armsAnsweringMoreThanOneValueOrFromDifferentPlacesAreNotRead() {
        assertEquals(List.of("kinds[*] RULE_ABOUT_A_DERIVED_VALUE"), notRead(countedOver(
                "kinds: List<Kind>", """
                        List.flatMap(k -> match k with
                            | WithKey { key, n } -> [ (key, n), (key, n) ]
                            | WithoutKey -> [], kinds)""")));
        assertEquals(List.of("nums[*] RULE_ABOUT_A_DERIVED_VALUE"), notRead(countedOver(
                "nums: List<Num>", "List.flatMap(a -> [ (a.key, a.n), (a.key, a.n) ], nums)")));
        assertEquals(List.of("nums[*] RULE_ABOUT_A_DERIVED_VALUE"), notRead(countedOver(
                "nums: List<Num>", """
                        List.flatMap(a -> if a.n > 3 then [ (a.key, a.n) ]
                                          else [ (String.append(a.key, "!"), a.n) ], nums)""")));
    }

    /**
     * The end of each key among the elements a statement keeps is the end among those of the key
     * that meet it, and is read as that: the same number of the same elements, with the statement
     * beside it.
     */
    @Test
    void theEndOfEachKeyAmongTheElementsAStatementKeepsIsOfThoseAlone() {
        assertEquals(List.of("least(nums[*].n kept by nums meeting Affine[form=LinearForm["
                        + "constant=-3, coefs={nums[*].n=1}], proposition=GT] by key)"
                        + " RULE_ABOUT_A_RUN"),
                notRead(leastOfKept("p.n", "List.filter(p -> p.n > 3, nums)")));
        assertEquals(List.of("least({1·n + 1 | nums[*]} kept by nums meeting Affine[form="
                        + "LinearForm[constant=-3, coefs={nums[*].n=1}], proposition=GT] by key)"
                        + " RULE_ABOUT_A_RUN"),
                notRead(leastOfKept("p.n + 1", "List.filter(p -> p.n > 3, nums)")));
        // Kept by two statements one after the other is kept by both, which is no one statement
        // a count reads.
        assertEquals(List.of("nums[*] RULE_ABOUT_A_DERIVED_VALUE"), notRead(leastOfKept("p.n",
                "List.filter(p -> p.n < 9, List.filter(p -> p.n > 3, nums))")));
    }

    /** A fold filing the least {@code value} of each key among the elements of {@code kept}. */
    private static String leastOfKept(String value, String kept) {
        return """
                behavior f : (nums: List<Num>) -> Report
                let f (nums) = {
                    let since: Map<String, Int> = List.fold(
                        (acc, p) -> Map.updateOrInsert(p.key, %s, seen -> Int.min(seen, %s), acc),
                        Map.empty, %s)
                    Report { stale = Map.keys(Map.filterEntries((k, v) -> v >= 30, since)) }
                }
                """.formatted(value, value, kept);
    }

    /** The kinds a case is written of, each a key and a number or a number alone. */
    private record AKind(String key, int n) {

        boolean withKey() {
            return key != null;
        }

        String written() {
            return withKey() ? "WithKey { key = \"" + key + "\", n = " + n + " }"
                    : "WithoutKey { n = " + n + " }";
        }
    }

    private static String written(List<AKind> kinds) {
        return "([" + String.join(", ", kinds.stream().map(AKind::written).toList()) + "])";
    }

    /** The kinds holding a key, as the numbers a list of them holds. */
    private static String writtenAsNums(List<AKind> kinds) {
        return "([" + String.join(", ", kinds.stream().filter(AKind::withKey)
                .map(each -> "Num { key = \"" + each.key() + "\", n = " + each.n() + " }")
                .toList()) + "])";
    }

    private static final List<List<AKind>> CASES = List.of(
            List.of(),
            List.of(new AKind(null, 4)),
            List.of(new AKind("a", 5)),
            List.of(new AKind("a", 5), new AKind(null, 1), new AKind("a", 2)),
            List.of(new AKind(null, 1), new AKind("b", 7), new AKind("a", 9), new AKind(null, 0)),
            List.of(new AKind("a", 3), new AKind("a", 8), new AKind("a", 1)));

    /** How many elements take the arm answering one, by the definition of the count. */
    private static int howManyMeet(List<AKind> kinds, Predicate<AKind> statement) {
        return (int) kinds.stream().filter(statement).count();
    }

    /** The least {@code n} of the elements of key {@code a} that meet {@code statement}, or -1. */
    private static int leastOfA(List<AKind> kinds, Predicate<AKind> statement) {
        Map<String, Integer> least = new LinkedHashMap<>();
        for (AKind each : kinds) {
            if (statement.test(each) && each.withKey()) {
                least.merge(each.key(), each.n(), Math::min);
            }
        }
        return least.getOrDefault("a", -1);
    }

    /** An activity: related to an account directly, through a deal, or to a lead, on a day. */
    private record AnAct(String how, String account, int on) {

        String written() {
            String related = switch (how) {
                case "account" -> "ToAccount { accountId = \"" + account + "\" }";
                case "deal" -> "ToDeal { accountId = \"" + account + "\", deal = \"d\" }";
                default -> "ToLead { lead = \"l\" }";
            };
            return "Act { related = " + related + ", on = " + on + " }";
        }
    }

    private static final List<List<AnAct>> ACTS = List.of(
            List.of(),
            List.of(new AnAct("lead", null, 1)),
            List.of(new AnAct("account", "a", 5)),
            List.of(new AnAct("deal", "a", 4), new AnAct("lead", null, 1),
                    new AnAct("account", "a", 6)),
            List.of(new AnAct("account", "b", 2), new AnAct("deal", "a", 9),
                    new AnAct("deal", "b", 1)),
            List.of(new AnAct("lead", null, 0), new AnAct("account", "a", 3),
                    new AnAct("deal", "a", 3)));

    /** The least day of account {@code a} among the activities related to an account, or -1. */
    private static int leastDayOfA(List<AnAct> acts) {
        return acts.stream().filter(each -> !"lead".equals(each.how()))
                .filter(each -> "a".equals(each.account())).mapToInt(AnAct::on).min().orElse(-1);
    }

    /**
     * The language computes, on every case, the numbers the readings say: how many elements take
     * the arm answering one, how often a key occurs among those, the least of each key among
     * the elements a statement keeps, and the least of each key read at the place the element's
     * case holds it.
     */
    @Test
    void theLanguageComputesWhatTheReadingsSay() {
        StringBuilder examples = new StringBuilder();
        StringBuilder held = new StringBuilder();
        StringBuilder least = new StringBuilder();
        StringBuilder leastOfTheCase = new StringBuilder();
        for (int i = 0; i < CASES.size(); i++) {
            List<AKind> kinds = CASES.get(i);
            examples.append("    | \"case ").append(i).append("\" : ").append(written(kinds))
                    .append(" -> ").append(howManyMeet(kinds, AKind::withKey)).append('\n');
            int ofA = (int) kinds.stream().filter(each -> "a".equals(each.key())).count();
            held.append("    | \"case ").append(i).append("\" : ").append(written(kinds))
                    .append(" -> ").append(ofA == 0 ? -1 : ofA).append('\n');
            least.append("    | \"case ").append(i).append("\" : ").append(writtenAsNums(kinds))
                    .append(" -> ").append(leastOfA(kinds, each -> each.n() > 3)).append('\n');
            leastOfTheCase.append("    | \"case ").append(i).append("\" : ")
                    .append(written(kinds)).append(" -> ")
                    .append(leastOfA(kinds, AKind::withKey)).append('\n');
        }
        StringBuilder leastDay = new StringBuilder();
        for (int i = 0; i < ACTS.size(); i++) {
            List<AnAct> acts = ACTS.get(i);
            leastDay.append("    | \"case ").append(i).append("\" : ([")
                    .append(String.join(", ", acts.stream().map(AnAct::written).toList()))
                    .append("]) -> ").append(leastDayOfA(acts)).append('\n');
        }
        Compilation compilation = Compilation.ofSource(HEAD + """
                behavior howMany : (kinds: List<Kind>) -> Int
                let howMany (kinds) = List.length(List.flatMap(k -> keysOf(k), kinds))

                behavior countOfA : (kinds: List<Kind>) -> Int
                let countOfA (kinds) = {
                    let pairs: List<(String, Int)> = List.flatMap(k -> pairsOf(k), kinds)
                    let since: Map<String, Int> = List.fold((acc, pair) -> {
                        let (key, n) = pair
                        Map.updateOrInsert(key, 1, seen -> seen + 1, acc)
                    }, Map.empty, pairs)
                    Map.get("a", since) |> Option.withDefault(0 - 1)
                }

                behavior leastOfA : (nums: List<Num>) -> Int
                let leastOfA (nums) = {
                    let since: Map<String, Int> = List.fold(
                        (acc, p) -> Map.updateOrInsert(p.key, p.n, seen -> Int.min(seen, p.n), acc),
                        Map.empty, List.filter(p -> p.n > 3, nums))
                    Map.get("a", since) |> Option.withDefault(0 - 1)
                }

                behavior leastOfTheCase : (kinds: List<Kind>) -> Int
                let leastOfTheCase (kinds) = {
                    let pairs: List<(String, Int)> = List.flatMap(k -> keysOf(k), kinds)
                    let since: Map<String, Int> = List.fold((acc, pair) -> {
                        let (key, n) = pair
                        Map.updateOrInsert(key, n, seen -> Int.min(seen, n), acc)
                    }, Map.empty, pairs)
                    Map.get("a", since) |> Option.withDefault(0 - 1)
                }

                behavior leastDayOfA : (acts: List<Act>) -> Int
                let leastDayOfA (acts) = {
                    let pairs: List<(String, Int)> = List.flatMap(a -> datesOf(a), acts)
                    let since: Map<String, Int> = List.fold((acc, pair) -> {
                        let (key, on) = pair
                        Map.updateOrInsert(key, on, seen -> Int.min(seen, on), acc)
                    }, Map.empty, pairs)
                    Map.get("a", since) |> Option.withDefault(0 - 1)
                }

                example howMany
                """ + examples + "\nexample countOfA\n" + held + "\nexample leastOfA\n" + least
                + "\nexample leastOfTheCase\n" + leastOfTheCase + "\nexample leastDayOfA\n"
                + leastDay, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
    }
}
