package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A sum is a common product times a choice of case, and the reading of one says both.
 *
 * <p>What every case spreads is stated of every value standing at the sum: a value of the sum was
 * built through one case's checked constructor, and every case carries the shared declaration, so
 * what that declaration writes holds here. What one case writes does not — it refuses values of that
 * case and not every value here — so it stays for the reading a {@code match} opens.
 *
 * <p><b>The two are independent, and this is the test that says so.</b> Each row below fixes one
 * combination of the two, and the pair in {@code aSumCanBothStateARuleAndLeaveOneToItsCases} is the
 * one an answer with a single arm cannot hold: dropping what is read here and dropping what is left
 * to the cases each turn a different assertion red.
 */
class ASumStatesWhatItsCasesShareAndLeavesTheCasesToAMatchTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static final String SOURCE = """
            module demo exposing ( Shared, Marked, Both, Quiet, Apart, Alone, keep )

            data NonNegInt = Int
                invariant value >= 0

            data Common = { amount: NonNegInt }
                invariant capped = amount.value <= 100

            data Plain = { ...Common }

            data Stamped = { ...Common, mark: NonNegInt }
                invariant stamped = mark.value >= 1

            data Shared = Plain | Plain

            data Both = Plain | Stamped

            data Quiet = { ...Common }

            data Marked = Quiet | Plain

            data OneWay = { a: NonNegInt }

            data OtherWay = { b: NonNegInt }

            data Apart = OneWay | OtherWay

            data Alone = { ...Common }

            behavior keep : (n: NonNegInt) -> NonNegInt

            let keep (n) = n
            """;

    private final Symbols symbols = symbols();

    private final PathEngine engine = new PathEngine(symbols, Map.of(),
            Terms.Of.THE_DISCHARGE_TREE, souther.compiler.query.ReadAs.THE_COMPILATION_DOES);

    private final GuaranteeWalk walk = new GuaranteeWalk(engine.guarantees());

    private static Symbols symbols() {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        compilation.answerEverything();
        return Scopes.derived(compilation.db(), compilation.modules().get(0)).value();
    }

    private Core.Read place(String name) {
        BindingId binding = CoreBinders
                .of(new Hir.Binders(new BindingOwner.OfValue("demo", "keep")).binder("v", POS))
                .binding();
        return new Core.Read("v", binding,
                Type.ref(TypeSymbols.declared(new TypeKey("demo", name))), POS);
    }

    /** What the walk was told, by the position it was told it at. */
    private record Told(Map<String, List<String>> guaranteed, List<String> handedOn) {}

    private Told reading(String name) {
        Core.Read root = place(name);
        Denotations at = Denotations.none().location(root.binding(),
                engine.terms().placeSubject(root.binding()),
                engine.terms().placeTerm(root.binding()));
        Map<String, List<String>> guaranteed = new LinkedHashMap<>();
        List<String> handedOn = new ArrayList<>();
        walk.from(root, FieldDomains.THE_VALUE, at, GuaranteeWalk.Scope.everyPosition(),
                new GuaranteeWalk.Reader() {
                    @Override
                    public void guaranteed(String path, TypeGuarantee guarantee) {
                        guaranteed.computeIfAbsent(path, _ -> new ArrayList<>())
                                .add(guarantee.rule().clause().toString());
                    }

                    @Override
                    public void handedOn(String path, Type type) {
                        // The value itself is at the empty path, which reads as nothing in a
                        // failure message. Named here so a diff says which position it was.
                        handedOn.add(path.isEmpty() ? "the value" : path);
                    }
                });
        return new Told(guaranteed, handedOn);
    }

    /** A record states its own rules here and leaves nothing to anybody. */
    @Test
    void aRecordStatesItsRulesHereAndLeavesNothing() {
        Told told = reading("Alone");

        assertTrue(states(told, "capped"), "the spread's rule is a rule about this value");
        assertEquals(List.of(), told.handedOn(),
                "nothing under a record waits for a reading somebody else opens");
    }

    /** A sum whose cases share nothing states nothing here, and every rule under it is a case's. */
    @Test
    void aSumSharingNothingStatesNothingAndLeavesEverything() {
        Told told = reading("Apart");

        assertEquals(Map.of(), told.guaranteed(),
                "a rule written on one case refuses values of that case, not every value here");
        assertEquals(List.of("the value"), told.handedOn(),
                "so the rules under it are for the reading a match opens");
    }

    /** A sum whose cases share a spread and write nothing of their own states the shared rules, and
     *  leaves nothing over: what a case carries is what was read here. */
    @Test
    void aSumWhoseCasesWriteNothingOfTheirOwnLeavesNothingOver() {
        Told told = reading("Marked");

        assertTrue(states(told, "capped"), "every case spreads Common, so Common holds here");
        assertEquals(List.of(), told.handedOn(),
                "the cases carry the shared rule and nothing besides, and it was read here");
    }

    /**
     * And the row a single answer cannot hold: rules read here, and rules left to the cases.
     *
     * <p>Both assertions are about one reading of one position. Stop reading what the cases share
     * and the first fails; stop saying that a case writes something of its own and the second does.
     * Neither failure implies the other, which is what makes the two independent rather than two
     * spellings of one.
     */
    @Test
    void aSumCanBothStateARuleAndLeaveOneToItsCases() {
        Told told = reading("Both");

        assertTrue(states(told, "capped"),
                "Plain and Stamped both spread Common, so what Common writes holds of either");
        assertFalse(states(told, "stamped"),
                "and what Stamped writes holds of a Stamped, not of every value here");
        assertEquals(List.of("the value"), told.handedOn(),
                "so Stamped's own rule is left for the reading a match opens");
    }

    /** The shared part is a position of its own, so what its type writes is read there. */
    @Test
    void theSharedFieldIsAPositionOfTheSum() {
        Told told = reading("Both");

        assertTrue(told.guaranteed().containsKey("amount"),
                "a field every case spreads is readable on the sum, and so are its rules: "
                        + told.guaranteed());
    }

    private static boolean states(Told told, String clause) {
        return told.guaranteed().values().stream().flatMap(List::stream)
                .anyMatch(each -> each.contains(clause));
    }
}
