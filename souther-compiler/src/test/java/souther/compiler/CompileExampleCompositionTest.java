package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An {@code example} on a {@code >->} composition: the stages run in order, and a case that leaves
 * the main line is what the row sees. What a single stage's example cannot state is the routing, so
 * these rows are the only compile-time statement of it.
 */
class CompileExampleCompositionTest {

    private static CompileException err(String model) {
        return assertThrows(CompileException.class, () -> Compiler.compile(model));
    }

    private static final String BASE = """
            module example.spike

            data Amount = Int
                invariant value >= 0

            data Draft = { amount: Amount }
            data Priced = { amount: Amount, fee: Amount }
            data TooSmall = { amount: Amount }
            data Receipt = { total: Amount }

            behavior price : (draft: Draft) -> Priced | TooSmall
                constructs Priced, TooSmall, Amount

            let price (draft) = {
                guard draft.amount.value >= 100 else TooSmall { amount = draft.amount }
                Priced { amount = draft.amount, fee = Amount(draft.amount.value / 10) }
            }

            behavior settle : (priced: Priced) -> Receipt
                constructs Receipt, Amount

            let settle (priced) =
                Receipt { total = Amount(priced.amount.value + priced.fee.value) }

            behavior priceAndSettle = price >-> settle
                -> Receipt | TooSmall
            """;

    @Test
    void aRowRunsTheStagesInOrder() {
        assertDoesNotThrow(() -> Compiler.compile(BASE + """
                example priceAndSettle
                  | "priced then settled" : (Draft { amount = Amount(1000) }) -> Receipt { total = Amount(1100) }
                """));
    }

    @Test
    void aCaseThatLeavesTheMainLineIsTheResult() {
        assertDoesNotThrow(() -> Compiler.compile(BASE + """
                example priceAndSettle
                  | "too small departs at the first stage" : (Draft { amount = Amount(10) }) -> TooSmall
                """));
    }

    @Test
    void aRowThatDoesNotHoldIsE1905() {
        assertEquals("E1905", err(BASE + """
                example priceAndSettle
                  | (Draft { amount = Amount(10) }) -> Receipt
                """).diagnostic().code());
    }

    /** The shape a composition is written for: a multi-input first stage, and a case retired by it. */
    private static final String MULTI = """
            module example.multi

            data Amount = Int
                invariant value >= 0

            data Committed = { id: String, floor: Amount }
            data Won = { id: String, wonAmount: Amount }
            data BelowFloor = { floor: Amount, offered: Amount }
            data Summary = { id: String, wonAmount: Amount }

            behavior close : (opp: Committed, on: String, finalAmount: Amount) -> Won | BelowFloor
                constructs Won, BelowFloor

            let close (opp, on, finalAmount) = {
                guard finalAmount.value >= opp.floor.value
                    else BelowFloor { floor = opp.floor, offered = finalAmount }
                Won { id = opp.id, wonAmount = finalAmount }
            }

            behavior summarize : (won: Won) -> Summary
                constructs Summary

            let summarize (won) =
                Summary { id = won.id, wonAmount = won.wonAmount }

            behavior closeAndSummarize = close >-> summarize
                -> Summary | BelowFloor
            """;

    @Test
    void aMultiInputFirstStageTakesTheRowsArguments() {
        assertDoesNotThrow(() -> Compiler.compile(MULTI + """
                example closeAndSummarize
                  | "won" : (Committed { id = "d-1", floor = Amount(100) }, "2026-07-30", Amount(200))
                        -> Summary { id = "d-1", wonAmount = Amount(200) }
                """));
    }

    @Test
    void aMultiInputFirstStageRetiresItsOwnCase() {
        assertDoesNotThrow(() -> Compiler.compile(MULTI + """
                example closeAndSummarize
                  | "below the floor" : (Committed { id = "d-1", floor = Amount(100) }, "2026-07-30", Amount(50))
                        -> BelowFloor { floor = Amount(100), offered = Amount(50) }
                """));
    }

    @Test
    void theRowsArityIsTheFirstStagesE1903() {
        assertEquals("E1903", err(MULTI + """
                example closeAndSummarize
                  | (Committed { id = "d-1", floor = Amount(100) }) -> BelowFloor
                """).diagnostic().code());
    }

    /** A named intermediate composition, and a function dependency of a later stage. */
    private static final String NESTED = """
            module example.nested

            data Amount = Int
                invariant value >= 0

            data Draft = { owner: String, amount: Amount }
            data Checked = { owner: String, amount: Amount }
            data Approved = { approver: String, amount: Amount }
            data Rejected = { reason: String }
            data Filed = { approver: String, amount: Amount }

            behavior check : (draft: Draft) -> Checked | Rejected
                constructs Checked, Rejected

            let check (draft) = {
                guard draft.amount.value > 0 else Rejected { reason = "zero" }
                Checked { owner = draft.owner, amount = draft.amount }
            }

            behavior bossOf : (owner: String) -> String

            behavior approve : (checked: Checked) -> Approved
                constructs Approved
                depends on bossOf

            let approve (checked, bossOf) =
                Approved { approver = bossOf(checked.owner), amount = checked.amount }

            behavior file : (approved: Approved) -> Filed
                constructs Filed

            let file (approved) =
                Filed { approver = approved.approver, amount = approved.amount }

            behavior half = check >-> approve
            behavior whole = half >-> file

            fake bossOf
                | ("e-1") -> "boss-1"
                | _       -> "unknown"
            """;

    @Test
    void aCompositionOfACompositionRunsItsStagesAndItsFakeTable() {
        assertDoesNotThrow(() -> Compiler.compile(NESTED + """
                example whole
                  | "filed" : (Draft { owner = "e-1", amount = Amount(10) })
                        -> Filed { approver = "boss-1", amount = Amount(10) }
                  | "rejected at the first stage" : (Draft { owner = "e-1", amount = Amount(0) })
                        -> Rejected { reason = "zero" }
                """));
    }

    @Test
    void theNamedIntermediateCarriesItsOwnExample() {
        assertDoesNotThrow(() -> Compiler.compile(NESTED + """
                example half
                  | (Draft { owner = "e-1", amount = Amount(10) })
                        -> Approved { approver = "boss-1", amount = Amount(10) }
                """));
    }

    /** A first stage that is itself injected: faked as the dependency it is. */
    private static final String INJECTED_FIRST = """
            module example.injectedfirst

            data Amount = Int
                invariant value >= 0

            data Rate = { pct: Int }
            data Priced = { amount: Amount }

            behavior rateFor : (currency: String) -> Rate

            behavior applyRate : (rate: Rate) -> Priced
                constructs Priced, Amount

            let applyRate (rate) =
                Priced { amount = Amount(rate.pct * 2) }

            behavior priceIn = rateFor >-> applyRate
            """;

    @Test
    void anInjectedFirstStageIsFakedAsADependency() {
        assertDoesNotThrow(() -> Compiler.compile(INJECTED_FIRST + """
                example priceIn
                  | ("JPY") with rateFor = Rate { pct = 50 } -> Priced { amount = Amount(100) }
                """));
    }

    /** Two stages naming the same injected behavior: the composition holds one field for it. */
    private static final String SHARED_DEP = """
            module example.shared

            data Amount = Int
                invariant value >= 0

            data A = { v: Amount }
            data B = { v: Amount }
            data C = { v: Amount }

            behavior bump : (v: Amount) -> Amount

            behavior one : (a: A) -> B
                constructs B
                depends on bump

            let one (a, bump) = B { v = bump(a.v) }

            behavior two : (b: B) -> C
                constructs C
                depends on bump

            let two (b, bump) = C { v = bump(b.v) }

            behavior both = one >-> two
            """;

    @Test
    void aDependencyTwoStagesShareIsFakedOnce() {
        assertDoesNotThrow(() -> Compiler.compile(SHARED_DEP + """
                example both
                  | (A { v = Amount(1) }) with bump = Amount(9) -> C { v = Amount(9) }
                """));
    }

    /** Each stage takes the fake it asked for, not the one next to it in the constructor. */
    @Test
    void eachStageTakesItsOwnFake() {
        String model = """
                module example.ordered

                data A = { v: String }
                data B = { v: String }
                data C = { v: String }

                behavior first : (v: String) -> String
                behavior second : (v: String) -> String

                behavior one : (a: A) -> B
                    constructs B
                    depends on first

                let one (a, first) = B { v = first(a.v) }

                behavior two : (b: B) -> C
                    constructs C
                    depends on second

                let two (b, second) = C { v = second(b.v) }

                behavior both = one >-> two

                example both
                  | (A { v = "in" }) with first = "1st", second = "2nd" -> C { v = "2nd" }
                """;
        assertDoesNotThrow(() -> Compiler.compile(model));
        // and the other way round does not hold, so the row above is not passing by symmetry
        String swapped = model.replace("-> C { v = \"2nd\" }", "-> C { v = \"1st\" }");
        assertEquals("E1905", err(swapped).diagnostic().code());
    }

    /** A row that departs before a stage runs still supplies that stage's fake: what a row needs is
     * a property of the composition, not of the path this input happens to take. */
    @Test
    void aDepartingRowStillSuppliesEveryFakeE1908() {
        String model = """
                module example.strict

                data Amount = Int
                    invariant value >= 0

                data Draft = { owner: String, amount: Amount }
                data Checked = { owner: String, amount: Amount }
                data Approved = { approver: String }
                data Rejected = { reason: String }

                behavior check : (draft: Draft) -> Checked | Rejected
                    constructs Checked, Rejected

                let check (draft) = {
                    guard draft.amount.value > 0 else Rejected { reason = "zero" }
                    Checked { owner = draft.owner, amount = draft.amount }
                }

                behavior bossOf : (owner: String) -> String

                behavior approve : (checked: Checked) -> Approved
                    constructs Approved
                    depends on bossOf

                let approve (checked, bossOf) =
                    Approved { approver = bossOf(checked.owner) }

                behavior decide = check >-> approve

                example decide
                  | "rejected before approval" : (Draft { owner = "e-1", amount = Amount(0) })
                        -> Rejected { reason = "zero" }
                """;
        CompileException e = err(model);
        assertEquals("E1908", e.diagnostic().code());
        assertDoesNotThrow(() -> Compiler.compile(
                model.replace("-> Rejected", "with bossOf = \"boss-1\" -> Rejected")));
    }

    /** The missing fake names the stage that wants it, not only the composition. */
    @Test
    void aMissingFakeNamesTheStageThatWantsIt() {
        CompileException e = err("""
                module example.whichstage

                data A = { v: String }
                data B = { v: String }
                data C = { v: String }

                behavior bossOf : (v: String) -> String

                behavior one : (a: A) -> B
                    constructs B

                let one (a) = B { v = a.v }

                behavior two : (b: B) -> C
                    constructs C
                    depends on bossOf

                let two (b, bossOf) = C { v = bossOf(b.v) }

                behavior both = one >-> two

                example both
                  | (A { v = "in" }) -> C { v = "out" }
                """);
        assertEquals("E1908", e.diagnostic().code());
        assertEquals("check.fake.missing.through", e.diagnostic().messageKey());
        assertEquals(List.of("both", "bossOf", "`two`"), List.of(e.diagnostic().args()));
    }

    /** A behavior asking for its own dependency reads as it did: there is no other stage to name. */
    @Test
    void aBehaviorsOwnMissingFakeReadsAsBefore() {
        CompileException e = err("""
                module example.ownfake

                data A = { v: String }
                data B = { v: String }

                behavior bossOf : (v: String) -> String

                behavior one : (a: A) -> B
                    constructs B
                    depends on bossOf

                let one (a, bossOf) = B { v = bossOf(a.v) }

                example one
                  | (A { v = "in" }) -> B { v = "out" }
                """);
        assertEquals("check.fake.missing", e.diagnostic().messageKey());
    }

    /** An injected behavior is still refused: it has nothing to run. */
    @Test
    void anInjectedTargetIsStillE1902() {
        assertEquals("E1902", err("""
                module example.injected

                data Priced = { amount: Int }

                behavior rateFor : (currency: String) -> Priced

                example rateFor
                  | ("JPY") -> Priced { amount = 1 }
                """).diagnostic().code());
    }

    /** E1902 has one reason left: the target is injected. */
    @Test
    void theRefusalReasonIsTheInjection() {
        CompileException e = err("""
                module example.injectedreason

                data Priced = { amount: Int }

                behavior rateFor : (currency: String) -> Priced

                example rateFor
                  | ("JPY") -> Priced { amount = 1 }
                """);
        String hint = String.valueOf(e.diagnostic().notes().get(0).args()[0]);
        assertTrue(hint.contains("injected"), hint);
        assertFalse(hint.contains(">->"), hint);
    }
}
