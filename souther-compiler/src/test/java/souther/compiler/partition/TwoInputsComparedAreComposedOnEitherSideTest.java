package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.DecisionEvidence;
import souther.compiler.query.RuleRequirement;
import souther.compiler.query.SettledAcross;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule comparing two inputs is offered a row on each side of the comparison: one where the two
 * hold one value and one where they hold two.
 *
 * <p>Read off the search that settles each rule of the decision, which composes a row, runs it and
 * keeps it only where the run took the rule — so a rule answered {@code Required} here is one a run
 * was seen taking, and the two values the row holds are equal or not as the run compared them, not
 * as their text reads.
 *
 * <p>Two strings stand on an order that counts nothing, so the comparison is two places on it held
 * against each other and not a sum; two records, two cases of a sum and two truths stand on no
 * order at all. Each is a way of comparing two inputs a row is composed for, and each is held here.
 */
class TwoInputsComparedAreComposedOnEitherSideTest {

    private static final String PASSWORDS = """
            module example.login

            data Password = String
            data Account = { password: Password }

            behavior f : (account: Account, given: Password) -> Allowed | Refused

            let f (account, given) =
                if account.password /= given then Refused else Allowed
            """;

    @Test
    void twoStringsAreOfferedARowWhereTheyDifferAndOneWhereTheyAreOne() {
        assertEveryRuleTaken(PASSWORDS);
        assertEveryRuleTaken(model("String", "a == b"));
        assertEveryRuleTaken(model("String", "a /= b"));
        assertEveryRuleTaken(model("String", "a < b"));
    }

    /** The same statement with its sides exchanged is the same one, and composed the same. */
    @Test
    void whichSideEachIsWrittenOnChangesNothing() {
        assertEveryRuleTaken(PASSWORDS.replace("account.password /= given",
                "given /= account.password"));
        Map<?, SettledAcross> twice = search("""
                module example.twice

                behavior f : (a: String, b: String) -> Int

                let f (a, b) =
                    (if a == b then 1 else 2) + (if b == a then 10 else 20)
                """, "f");
        assertEquals(2, twice.size(),
                () -> "a == b and b == a are one distinction, so two rules and not four: " + twice);
        twice.values().forEach(each -> assertInstanceOf(RuleRequirement.Required.class,
                each.requirement(), () -> "each taken by its row: " + each));
    }

    @Test
    void twoValuesOnNoOrderAreOfferedARowEachWay() {
        assertEveryRuleTaken("""
                module example.points

                data Point = { x: Int, y: Int }

                behavior f : (a: Point, b: Point) -> Int

                let f (a, b) =
                    if a == b then 1 else 2
                """);
        assertEveryRuleTaken("""
                module example.shapes

                data Circle = { r: Int }
                data Square = { s: Int }
                data Shape = Circle | Square

                behavior f : (a: Shape, b: Shape) -> Int

                let f (a, b) =
                    if a /= b then 1 else 2
                """);
        assertEveryRuleTaken(model("Bool", "a == b"));
    }

    /**
     * A value read under a case of a sum is read off that case's record, so two values one of them
     * is read under a case are composed the same way.
     */
    @Test
    void aValueReadUnderACaseIsComposedAsOneReadBare() {
        assertEveryRuleTaken("""
                module example.undercase

                data P = { n: Int }
                data Circle = { p: P }
                data Square = { s: Int }
                data Shape = Circle | Square

                behavior f : (a: Shape, b: P) -> Int

                let f (a, b) =
                    match a with
                        | Circle as c -> if c.p /= b then 1 else 2
                        | Square -> 3
                """);
    }

    /**
     * The arm a comparison of two strings leads into is one a way in is read for: the comparison
     * coming out that way, said of the strings it compares. Not the arm itself as the only way in,
     * which is what a reading falls back on where the ways into an arm cannot all be written down
     * and which nothing composes a row from.
     */
    @Test
    void theArmTheComparisonLeadsIntoIsReadAsTheComparisonComingOutThatWay() {
        Compilation compilation = compiled(PASSWORDS + """

                example f
                    | (Account { password = Password("") }, Password("")) -> Allowed
                """);
        List<Adequacy.GenerationDisposition> arms =
                Adequacy.generatedOf(compilation.db(), "example.login").get("f").generation()
                        .stream()
                        .filter(each -> each.finding().kind() == Adequacy.Kind.ARM_UNREACHED)
                        .toList();
        assertEquals(1, arms.size(), () -> "the arm a wrong password takes: " + arms);
        assertFalse(arms.getFirst().outcome() instanceof GenerationOutcome.NotSupported,
                () -> "a way into it is read: " + arms);
    }

    /**
     * The arm a comparison of two records, two cases of a sum or two truths leads into is offered
     * a row the same way, by the walk that composes a row for a coverage item rather than for a
     * rule of the decision.
     */
    @Test
    void theArmTwoValuesOnNoOrderLeadIntoIsOfferedARow() {
        assertTheArmIsOfferedARow("""
                module example.armpoints

                data Point = { x: Int, y: Int }

                behavior f : (a: Point, b: Point) -> Same | Apart

                let f (a, b) =
                    if a /= b then Apart else Same

                example f
                    | (Point { x = 0, y = 0 }, Point { x = 0, y = 0 }) -> Same
                """);
        assertTheArmIsOfferedARow("""
                module example.armshapes

                data Circle = { r: Int }
                data Square = { s: Int }
                data Shape = Circle | Square

                behavior f : (a: Shape, b: Shape) -> Same | Apart

                let f (a, b) =
                    if a /= b then Apart else Same

                example f
                    | (Circle { r = 0 }, Circle { r = 0 }) -> Same
                """);
        assertTheArmIsOfferedARow("""
                module example.armtruths

                behavior f : (a: Bool, b: Bool) -> Same | Apart

                let f (a, b) =
                    if a /= b then Apart else Same

                example f
                    | (true, true) -> Same
                """);
    }

    /**
     * A value held with another at a field of it is handed on where the field is already held at
     * a value: the other is given the value the field holds, and not one a type offers first.
     */
    @Test
    void aValueHeldWithAFieldHeldAtAValueIsGivenTheValueTheFieldHolds() {
        assertEveryRuleTaken("""
                module example.samefield

                data P = { n: Int }
                data Q = { p: P }

                behavior f : (a: Q, b: P) -> Int

                let f (a, b) =
                    if a.p.n == 7 && a.p == b then 1 else 2
                """);
    }

    /**
     * What the way asks under the second of two values held to one is asked of the first as well:
     * one value at both is one value, and the first composed alone is one the second cannot be.
     */
    @Test
    void whatIsAskedUnderEitherOfTwoValuesHeldToOneIsAskedOfBoth() {
        assertEveryRuleTaken("""
                module example.later

                data P = { n: Int }

                behavior f : (a: P, b: P) -> Int

                let f (a, b) =
                    if a == b && b.n == 7 then 1 else 2
                """);
    }

    /**
     * Two strings a rule allows only a few values of are held apart among those values: the place
     * the way leaves one is tried at each value the rule names, and not only at the first.
     */
    @Test
    void stringsARuleNamesTheValuesOfAreHeldApartAmongThem() {
        assertEveryRuleTaken("""
                module example.named

                data Code = String
                    invariant value == "a" || value == "b"

                behavior f : (a: Code, b: Code) -> Int

                let f (a, b) =
                    if a /= b && b == "a" then 1 else 2
                """);
        assertEveryRuleTaken("""
                module example.namedthree

                data Code = String
                    invariant value == "a" || value == "b"

                behavior f : (a: Code, b: Code, c: Code) -> Int

                let f (a, b, c) =
                    if a /= b && c == b && c == "a" then 1 else 2
                """);
    }

    /** Two positions of one parameter held to one value, or two, are composed as two would be. */
    @Test
    void twoPositionsOfOneParameterAreComposedOnEitherSide() {
        assertEveryRuleTaken("""
                module example.sameinone

                data P = { n: Int }
                data Pair = { left: P, right: P }

                behavior f : (p: Pair) -> Int

                let f (p) =
                    if p.left.n == 7 && p.left == p.right then 1 else 2
                """);
        assertEveryRuleTaken("""
                module example.apartinone

                data Pair = { left: String, right: String }

                behavior f : (p: Pair) -> Int

                let f (p) =
                    if p.left /= p.right then 1 else 2
                """);
    }

    /**
     * Three values each other than the other two are composed for every type that has three: a
     * value held apart from two is offered among one more value than it is to avoid, and not
     * among a fixed number of them.
     */
    @Test
    void threeValuesApartAreOfferedOneMoreValueThanEachAvoids() {
        assertEveryRuleTaken(model3("String"));
        assertEveryRuleTaken("""
                module example.three

                data P = { n: Int }

                behavior f : (a: P, b: P, c: P) -> Int

                let f (a, b, c) =
                    if a /= b && a /= c && b /= c then 1 else 2
                """);
    }

    /**
     * Two truths cannot be three values apart, and what the search says is that it composed
     * nothing — not that the rule is out of reach, which nothing here shows.
     */
    @Test
    void threeTruthsApartAreNotSaidToBeOutOfReach() {
        Map<?, SettledAcross> settled = search(model3("Bool"), "f");
        assertEquals(1, settled.values().stream()
                .filter(each -> each.requirement()
                        instanceof RuleRequirement.Required).count(),
                () -> "only the way past the else is taken: " + settled);
        for (SettledAcross each : settled.values()) {
            assertFalse(each.requirement() instanceof RuleRequirement.Excluded,
                    () -> "running out of values is no proof: " + each);
        }
    }

    /** Two statements about three inputs, met by one row together. */
    @Test
    void twoComparisonsAreMetTogether() {
        assertEveryRuleTaken("""
                module example.three

                behavior f : (a: String, b: String, c: String) -> Int

                let f (a, b, c) =
                    if a == b && b /= c then 1 else 2
                """);
    }

    /**
     * A way asking two inputs to be one value and two at once is offered no row, and is not said
     * to be taken — whichever value the first comparison left the two at.
     */
    @Test
    void aWayAskingTheTwoToBeOneAndTwoIsTakenByNoRowComposedForIt() {
        Map<?, SettledAcross> settled = search("""
                module example.contradiction

                behavior f : (a: String, b: String) -> Int

                let f (a, b) =
                    if a == b && a /= b then 1 else 2
                """, "f");
        List<RuleRequirement> requirements = settled.values().stream()
                .map(each -> each.requirement()).toList();
        assertEquals(1, requirements.stream().filter(RuleRequirement.Required.class::isInstance)
                .count(), () -> "the way past the else is taken and the other is not: "
                + requirements);
    }

    /** Of two codes only two values admit, the second value is tried where the first is the
     *  other's. */
    @Test
    void whereTheFirstValueTriedIsTheOthersTheNextIsTried() {
        assertEveryRuleTaken("""
                module example.codes

                data Code = String
                    invariant value == "a" || value == "b"

                behavior f : (a: Code, b: Code) -> Int

                let f (a, b) =
                    if a /= b then 1 else 2
                """);
    }

    /**
     * Where no two values tried differ, the rule is one this search found no row for and not one
     * the model leaves no row: the values it tried are what it had, and nothing proved there are
     * no others.
     */
    @Test
    void whereNothingTriedDiffersTheRuleIsNotSaidToBeOutOfReach() {
        Map<?, SettledAcross> settled = search("""
                module example.code

                data Code = String
                    invariant value == "a"

                behavior f : (a: Code, b: Code) -> Int

                let f (a, b) =
                    if a /= b then 1 else 2
                """, "f");
        for (SettledAcross each : settled.values()) {
            assertFalse(each.requirement() instanceof RuleRequirement.Excluded,
                    () -> "nothing here shows the rule is out of reach: " + each);
        }
    }

    private static String model(String type, String condition) {
        return """
                module example.two

                behavior f : (a: TYPE, b: TYPE) -> Int

                let f (a, b) =
                    if (CONDITION) then 1 else 2
                """.replace("TYPE", type).replace("CONDITION", condition);
    }

    private static String model3(String type) {
        return """
                module example.three

                behavior f : (a: TYPE, b: TYPE, c: TYPE) -> Int

                let f (a, b, c) =
                    if a /= b && a /= c && b /= c then 1 else 2
                """.replace("TYPE", type);
    }

    /**
     * The one arm the example leaves untaken is read as the comparison coming out the other way,
     * and the rule saying so is taken by the row composed for it.
     */
    private static void assertTheArmIsOfferedARow(String model) {
        Compilation compilation = compiled(model);
        String module = compilation.modules().getFirst();
        List<Adequacy.GenerationDisposition> arms =
                Adequacy.generatedOf(compilation.db(), module).get("f").generation().stream()
                        .filter(each -> each.finding().kind() == Adequacy.Kind.ARM_UNREACHED)
                        .toList();
        assertEquals(1, arms.size(), () -> "the arm the values apart take: " + arms);
        assertFalse(arms.getFirst().outcome() instanceof GenerationOutcome.NotSupported,
                () -> "a way into it is read:\n" + model + "\n" + arms);
        Map<?, SettledAcross> settled =
                compilation.db().ask(new Adequacy.DecisionSearch(module, "f")).value();
        assertEquals(1, settled.size(), () -> "the rule the example leaves: " + settled);
        assertInstanceOf(RuleRequirement.Required.class,
                settled.values().iterator().next().requirement(),
                () -> "a row whose run takes the arm:\n" + model + "\n" + settled);
    }

    private static void assertEveryRuleTaken(String model) {
        Map<?, SettledAcross> settled = search(model, "f");
        assertTrue(settled.size() >= 2, () -> "a rule each way: " + settled);
        for (SettledAcross each : settled.values()) {
            assertInstanceOf(RuleRequirement.Required.class, each.requirement(),
                    () -> "a row whose run took the rule:\n" + model + "\n" + each);
        }
    }

    /** What the search came to for each rule the rows written leave untaken, which is every rule
     *  here: no row is written. */
    private static Map<?, SettledAcross> search(String model, String behavior) {
        Compilation compilation = compiled(model);
        String module = compilation.modules().getFirst();
        DecisionEvidence evidence = compilation.db().ask(new Adequacy.Decides(module)).value()
                .get(behavior);
        assertEquals(evidence.read().rules().size(), evidence.notTakenByRows().size(),
                "no row is written, so no rule is taken");
        return compilation.db().ask(new Adequacy.DecisionSearch(module, behavior)).value();
    }

    private static Compilation compiled(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
