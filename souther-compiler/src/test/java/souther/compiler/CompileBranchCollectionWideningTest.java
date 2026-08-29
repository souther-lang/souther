package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two joined positions ({@code if} branches, {@code match} arms) widen under a covariant
 * constructor, not only at the top: a list of one case and a list of another join to a list of
 * their union, as {@code ++} already does (spec §unmarked-output, §if). Before this, the merge only knew
 * three answers — the two types are equal, one is an empty-collection bottom, or both are data-like
 * — so a {@code List} on each side fell through to a disagreement.
 */
class CompileBranchCollectionWideningTest {

    private static final String HEAD = """
            module demo
            data Costly = { threshold: Int }
            data NoAuthority
            data PaidByOther
            data Reason = Costly | NoAuthority | PaidByOther
            data Reasons = { reasons: List<Reason> }
            """;

    /** {@code behavior make} building the cases {@code names} lists, on top of {@link #HEAD}. */
    private static String makeBuilding(String names) {
        return HEAD + "behavior make : (total: Int) -> Reasons constructs Reasons, " + names + "\n";
    }

    @Test
    void oneArmEmptyWithADeclaredReturnType() {
        // the declared return reaches both arms, so `[]` is already a List<Reason> and no longer the
        // bottom the merge used to absorb — the widening has to carry the join on its own
        assertDoesNotThrow(() -> Compiler.compile(makeBuilding("Costly") + """
                let reasons (total: Int): List<Reason> =
                    if total >= 100 then [ Costly { threshold = 100 } ] else []
                let make (total) = Reasons { reasons = reasons(total) }
                """));
    }

    @Test
    void bothArmsNonEmptyListsOfDifferentCases() {
        assertDoesNotThrow(() -> Compiler.compile(makeBuilding("Costly") + """
                let reasons (total: Int): List<Reason> =
                    if total >= 100 then [ Costly { threshold = 100 } ] else [ NoAuthority ]
                let make (total) = Reasons { reasons = reasons(total) }
                """));
    }

    @Test
    void matchArmsOfDifferentCaseLists() {
        assertDoesNotThrow(() -> Compiler.compile(makeBuilding("Costly") + """
                data Big
                data Small
                data Size = Big | Small
                let reasons (size: Size): List<Reason> =
                    match size with
                    | Big -> [ Costly { threshold = 100 } ]
                    | Small -> [ NoAuthority ]
                let sizeOf (total: Int): Size = if total >= 100 then Big else Small
                let make (total) = Reasons { reasons = reasons(sizeOf(total)) }
                """));
    }

    @Test
    void noExpectedTypeInScope() {
        // a local binding with no annotation: nothing pushes List<Reason> down, so the join is the
        // only thing that can widen the two arms
        assertDoesNotThrow(() -> Compiler.compile(makeBuilding("Costly") + """
                let make (total) = {
                    let rs = if total >= 100 then [ Costly { threshold = 100 } ] else [ NoAuthority ]
                    Reasons { reasons = rs }
                }
                """));
    }

    @Test
    void setArmsOfDifferentCases() {
        assertDoesNotThrow(() -> Compiler.compile(HEAD + """
                data ReasonSet = { reasons: Set<Reason> }
                behavior collect : (total: Int) -> ReasonSet constructs ReasonSet, Costly
                let reasons (total: Int): Set<Reason> =
                    if total >= 100
                        then Set.insert(Costly { threshold = 100 }, Set.empty)
                        else Set.insert(NoAuthority, Set.empty)
                let collect (total) = ReasonSet { reasons = reasons(total) }
                """));
    }

    /** Two cases with a field each, so a {@code Map} value and an optional field have a decoder. */
    private static final String GRADES = """
            module demo
            data Fine = { code: String }
            data Rough = { code: String }
            data Grade = Fine | Rough
            """;

    @Test
    void optionArmsOfDifferentCases() {
        // an optional is written on a data field only, so the field type is what the two arms meet at
        assertDoesNotThrow(() -> Compiler.compile(GRADES + """
                data Held = { fine: Fine?, rough: Rough? }
                data Picked = { grade: Grade? }
                behavior pick : (h: Held, high: Bool) -> Picked constructs Picked
                let pick (h, high) = Picked { grade = if high then h.fine else h.rough }
                """));
    }

    @Test
    void mapValueArmsOfDifferentCases() {
        assertDoesNotThrow(() -> Compiler.compile(GRADES + """
                data Held = { fine: Map<String, Fine>, rough: Map<String, Rough> }
                data Picked = { byCode: Map<String, Grade> }
                behavior pick : (h: Held, high: Bool) -> Picked constructs Picked
                let byCode (h: Held, high: Bool): Map<String, Grade> =
                    if high then h.fine else h.rough
                let pick (h, high) = Picked { byCode = byCode(h, high) }
                """));
    }

    @Test
    void tupleOfCaseListsInEachArm() {
        assertDoesNotThrow(() -> Compiler.compile(makeBuilding("Costly") + """
                let reasons (total: Int): (List<Reason>, Int) =
                    if total >= 100 then ([ Costly { threshold = 100 } ], 1) else ([ NoAuthority ], 0)
                let make (total) = {
                    let (rs, n) = reasons(total)
                    Reasons { reasons = rs }
                }
                """));
    }

    @Test
    void nestedListElementsOfDifferentCases() {
        // the element rule that types a literal and `++` is the same join, so it descends too
        assertDoesNotThrow(() -> Compiler.compile(makeBuilding("Costly") + """
                data Grouped = { groups: List<List<Reason>> }
                behavior group : () -> Grouped constructs Grouped, Costly
                let group = Grouped { groups = [ [ Costly { threshold = 100 } ], [ NoAuthority ] ] }
                let make (total) = Reasons { reasons = [ Costly { threshold = 100 }, NoAuthority ] }
                """));
    }

    @Test
    void armsThatShareNoTypeAreStillRejected() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile(makeBuilding("Costly") + """
                let reasons (total: Int): List<Reason> =
                    if total >= 100 then [ Costly { threshold = 100 } ] else [ 1 ]
                let make (total) = Reasons { reasons = reasons(total) }
                """));
        assertTrue(e.getMessage().contains("branches"), e.getMessage());
    }

    @Test
    void theWidenedListRunsAndCarriesBothCases() throws Exception {
        String src = """
                module demo
                data Costly = { threshold: Int }
                data NoAuthority
                data Reason = Costly | NoAuthority
                data Trip = { total: Int }
                data Reasons = { reasons: List<Reason> }
                behavior decide : (t: Trip) -> Reasons constructs Reasons, Costly
                let reasons (total: Int): List<Reason> =
                    if total >= 100 then [ Costly { threshold = 100 } ] else [ NoAuthority ]
                let decide (t) = Reasons { reasons = reasons(t.total) }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object impl = Emitted.behavior(loader, "demo", "decide").getConstructor().newInstance();

        assertEquals(Map.of("type", "Costly", "threshold", 100L), reasons(loader, impl, 100).get(0));
        assertEquals(Map.of("type", "NoAuthority"), reasons(loader, impl, 1).get(0));
    }

    @Test
    void theWidenedListRunsWhenOneArmIsEmpty() throws Exception {
        // the join is List<Costly | Reason> here, not a plain List<Reason>: the case built on one
        // arm and the sum the empty arm adopted, unioned. The backend has to emit from that too.
        String src = """
                module demo
                data Costly = { threshold: Int }
                data NoAuthority
                data Reason = Costly | NoAuthority
                data Trip = { total: Int }
                data Reasons = { reasons: List<Reason> }
                behavior decide : (t: Trip) -> Reasons constructs Reasons, Costly
                let reasons (total: Int): List<Reason> =
                    if total >= 100 then [ Costly { threshold = 100 } ] else []
                let decide (t) = Reasons { reasons = reasons(t.total) }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object impl = Emitted.behavior(loader, "demo", "decide").getConstructor().newInstance();

        assertEquals(Map.of("type", "Costly", "threshold", 100L), reasons(loader, impl, 100).get(0));
        assertEquals(List.of(), reasons(loader, impl, 1));
    }

    private List<?> reasons(BytesClassLoader loader, Object impl, long total) throws Exception {
        Object trip = Codecs.decoded(loader, "demo.Trip", Map.of("total", total));
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Reasons", Codecs.apply(impl, trip));
        return (List<?>) out.get("reasons");
    }
}
