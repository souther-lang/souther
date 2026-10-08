package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.check.RuleKey;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;
import souther.compiler.partition.DecidedCondition;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.DecisionRule;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.partition.OnTheWay;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.DecisionEvidence;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A fork on a name every case of a sum spreads is a narrowing of the value at that name, which
 * stands under whichever case the row turns out to be.
 *
 * <p>{@code r.q.flag} is no position: the value stands at {@code r.q@A.flag} or at
 * {@code r.q@B.flag}. Each arm of a fork on it is a narrowing on the way and a column of its own,
 * what it requires moves under the case once one is chosen, and a row composed for it holds the
 * arm's case under whichever case it is written as.
 */
class AForkOnANameTheCasesShareIsANarrowingTest {

    private static final String MODEL = """
            module probe.shared exposing ( Yes, No, Flag, Common, A, B, Q, Req, decide )

            data Yes
            data No
            data Flag = Yes | No
            data Common = { flag: Flag }
            data A = { ...Common, a: Int }
            data B = { ...Common, b: Int }
            data Q = A | B
            data Req = { q: Q }

            behavior decide : (r: Req) -> String
            let decide (r) =
                match r.q.flag with
                    | Yes -> "yes"
                    | No -> "no"

            data Renkei
            data Unit = Q | Renkei
            data Floor = { unit: Unit }

            behavior staffed : (f: Floor) -> String
            let staffed (f) =
                match f.unit with
                    | Q as x ->
                        match x.flag with
                            | Yes -> "yes"
                            | No -> "no"
                    | Renkei -> "linked"

            data A1 = { ...Common, one: Int }
            data A2 = { ...Common, two: Int }
            data Deep = A1 | A2
            data D = { ...Common, deep: Int }
            data Outer = Deep | D
            data Nest = { o: Outer }

            behavior nested : (n: Nest) -> String
            let nested (n) =
                match n.o.flag with
                    | Yes -> "yes"
                    | No -> "no"
            """;

    /** Each arm narrows the name, and the arms are the answers of one column about it. */
    @Test
    void eachArmIsANarrowingOnTheWayAndAColumnOfItsOwn() {
        List<DecisionReading.Ruled> ruled = ruledOf("decide");
        assertEquals(2, ruled.size(), () -> "a rule per arm: " + ruled);
        for (DecisionReading.Ruled each : ruled) {
            List<OnTheWay> onTheWay = each.states().onTheWay();
            assertTrue(onTheWay.stream().allMatch(step -> step instanceof OnTheWay.Narrowed),
                    () -> "the arm is read as a narrowing: " + onTheWay);
            assertTrue(each.states().declined().isEmpty(),
                    () -> "and nothing on the way is declined: " + each);
        }
        assertEquals(List.of(List.of("r.q.flag -> Yes"), List.of("r.q.flag -> No")),
                ruled.stream().map(each -> answers(each.rule())).toList());
    }

    /** What the body tells apart at the positions under each case is the fork. */
    @Test
    void thePartitionDoesNotSayTheBodyLeavesTheNameUndivided() {
        String human = report();
        for (String position : List.of("r.q@A.flag", "r.q@B.flag", "n.o@A1.flag", "n.o@A2.flag",
                "n.o@D.flag", "f.unit@A.flag", "f.unit@B.flag")) {
            assertFalse(human.contains(position + " holds"),
                    () -> position + " is told apart by the fork:\n" + human);
        }
    }

    /**
     * What the arm requires is at the name until a case is chosen, and then at the position under
     * that case — where a class asking the other case of the flag is a conflict with it.
     */
    @Test
    void theArmsRequirementMovesUnderTheCaseAndMeetsWhatIsAskedThere() {
        Requirements yes = mergedOf(wayThrough("decide", "r.q.flag -> Yes"));
        assertEquals(List.of(path("r", "q", "flag")), yes.atANameTheCasesShare(),
                "no case is chosen for it, so it stays at the name");
        assertEquals(null, yes.at(underTheCase("r", "q", "A", "flag")));

        Requirements asA = assertInstanceOf(Requirements.Merge.Merged.class,
                yes.merge(caseAt("r", "q", "A"))).requirements();
        assertEquals("Yes", asA.at(underTheCase("r", "q", "A", "flag")).spelled(),
                () -> "written as an A, the flag is A's: " + asA);
        assertEquals(null, asA.at(path("r", "q", "flag")), () -> "and not the name's: " + asA);
        assertEquals(List.of(), asA.crossings(), () -> "nothing is left to cross: " + asA);

        Requirements aClassAskingNo = assertInstanceOf(Requirements.Merge.Merged.class,
                caseAt("r", "q", "A").merge(flagAt(underTheCase("r", "q", "A", "flag"), "No")))
                .requirements();
        Requirements.Merge.Conflict against = assertInstanceOf(Requirements.Merge.Conflict.class,
                yes.merge(aClassAskingNo));
        assertEquals(underTheCase("r", "q", "A", "flag"), against.at());
    }

    /**
     * A row is composed for every arm, and holds the arm's case under whichever case it is written
     * as.
     *
     * <p>Composed, and not left for want of a case: the way says what the value at the name is, and
     * a row is one case or another — so what it asks is written under each case in turn until one
     * composes. A rule nothing could show a row for is one the search stopped short of.
     */
    @Test
    void aRowForTheArmHoldsItsCaseUnderTheCaseItIsWrittenAs() {
        String human = report();
        assertFalse(human.contains("nothing could show a row can be written"), human);
        String block = offered();
        assertTrue(block.contains("q = A { flag = Yes")
                        && block.contains("q = B { flag = Yes"),
                () -> "each case is written with the flag the arm asks:\n" + block);
    }

    /**
     * On a value a fork left several cases, the name is the one the cases share, and the arm
     * inside narrows it the same way.
     */
    @Test
    void aNameOnAValueLeftSeveralCasesIsReadTheSameWay() {
        List<DecisionReading.Ruled> ruled = ruledOf("staffed");
        assertTrue(ruled.stream().map(each -> answers(each.rule())).toList().contains(
                        List.of("f.unit -> {A|B}", "f.unit.flag -> Yes")),
                () -> "the arm inside narrows the shared name: " + ruled);
        Requirements yes = mergedOf(wayThrough("staffed", "f.unit.flag -> Yes"));
        assertEquals(List.of(path("f", "unit", "flag")), yes.atANameTheCasesShare(),
                "a value left A or B is no case in particular, so it stays at the name");
        Requirements asB = assertInstanceOf(Requirements.Merge.Merged.class,
                yes.merge(caseAt("f", "unit", "B"))).requirements();
        assertEquals("Yes", asB.at(underTheCase("f", "unit", "B", "flag")).spelled(),
                () -> "written as a B, the flag is B's: " + asB);
    }

    /** A name two sums down moves under both before it stands anywhere. */
    @Test
    void aNameTwoSumsDownMovesUnderBoth() {
        Requirements yes = mergedOf(wayThrough("nested", "n.o.flag -> Yes"));
        Requirements asA1 = assertInstanceOf(Requirements.Merge.Merged.class,
                yes.merge(caseAt("n", "o", "A1"))).requirements();
        assertEquals("Yes", asA1.at(underTheCase("n", "o", "A1", "flag")).spelled(),
                () -> "the flag is A1's: " + asA1);
        assertEquals(List.of(), asA1.atANameTheCasesShare(), () -> asA1.toString());
    }

    private static Requirements mergedOf(DecisionReading.Ruled ruled) {
        return assertInstanceOf(Requirements.Merge.Merged.class, ruled.states().requirements(),
                () -> "a row can take the way: " + ruled).requirements();
    }

    /** That the value at {@code head.sum} is the case named {@code leaf}, as the flag under that
     *  case requires it. */
    private static Requirements caseAt(String head, String sum, String leaf) {
        TermPath under = underTheCase(head, sum, leaf, "flag");
        Requirements required = under.requirements();
        assertNotNull(required.at(path(head, sum)), () -> under + " is under a case of " + sum);
        return required;
    }

    /** That the flag at {@code at} is what the arm of {@code decide} naming {@code leaf} leaves
     *  it. */
    private static Requirements flagAt(TermPath at, String leaf) {
        CasesLeft named = wayThrough("decide", "r.q.flag -> " + leaf).states().onTheWay()
                .stream()
                .filter(each -> each instanceof OnTheWay.Narrowed)
                .map(each -> ((OnTheWay.Narrowed) each).position().narrowing())
                .findFirst().orElseThrow();
        return Requirements.NONE.and(at, named);
    }

    private static TermPath path(String head, String... fields) {
        TermPath out = TermPath.of(head);
        for (String each : fields) {
            out = out.then(each);
        }
        return out;
    }

    /** {@code head.sum@leaf.field}, as the reading of the input holds it. */
    private static TermPath underTheCase(String head, String sum, String leaf, String field) {
        Compilation c = measured();
        for (InputDomain inputs : c.db().ask(new Adequacy.Inputs(c.modules().get(0))).value()
                .values()) {
            for (TermPath each : inputs.positionsNamed(TermPath.of(head),
                    new RuleKey(List.of(sum, field)))) {
                if (each.toString().equals(head + "." + sum + "@" + leaf + "." + field)) {
                    return each;
                }
            }
        }
        throw new AssertionError("no position " + head + "." + sum + "@" + leaf + "." + field);
    }

    private static DecisionReading.Ruled wayThrough(String behavior, String answer) {
        return ruledOf(behavior).stream()
                .filter(each -> answers(each.rule()).contains(answer))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "a rule of " + behavior + " goes through " + answer));
    }

    /** Each case column of {@code rule}, as its subject and what the rule came out as. */
    private static List<String> answers(DecisionRule rule) {
        return rule.inOrder().stream()
                .filter(each -> each instanceof DecidedCondition.Narrowed)
                .map(each -> (DecidedCondition.Narrowed) each)
                .map(each -> ((DecisionSubject.AnInput) each.condition().of()).at() + " -> "
                        + each.to().spelled())
                .toList();
    }

    private static List<DecisionReading.Ruled> ruledOf(String behavior) {
        Compilation c = measured();
        DecisionEvidence decided = c.db().ask(new Adequacy.Decides(c.modules().get(0))).value()
                .get(behavior);
        assertNotNull(decided, () -> "the rules of " + behavior + " are read");
        return decided.read().found();
    }

    private static String report() {
        Compilation c = measured();
        return AdequacyReport.of(c).human(SourceRendering.namedByIdentity(c.texts()));
    }

    private static String offered() {
        Compilation c = measured();
        return GeneratedRows.of(
                Adequacy.offeredFor(c.db(), OfferingRequest.overTheModule("probe.shared")),
                Map.of(), SourceRendering.namedByIdentity(c.texts()), c.db()).text();
    }

    /** The model measured once for every question here: each asks of the one measurement, and
     *  none of them changes it. */
    private static Compilation measured() {
        Compilation c = Measured.ONCE;
        assertEquals(List.of(), c.errors().stream()
                .map(e -> e.diagnostic().code() + " " + e.diagnostic().said()).toList(),
                "the model is measured");
        return c;
    }

    private static final class Measured {

        static final Compilation ONCE = measure();

        private static Compilation measure() {
            Compilation c = Compilation.ofSource(MODEL, "Main");
            c.measure(Adequacy.Asked.fullReport());
            c.answerEverything();
            return c;
        }
    }
}
