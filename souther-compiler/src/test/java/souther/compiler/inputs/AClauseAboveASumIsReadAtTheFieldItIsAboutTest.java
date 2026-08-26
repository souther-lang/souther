package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A clause of the value a sum sits in names a field the cases share, and that field is under a case.
 *
 * <p>So the clause is read where the field is. What crosses the narrowing is the name — the clause
 * stays where it was written, and the end it draws is the one it drew: an author sent to look at it
 * is sent to the declaration that wrote it and not to the case the reading came through.
 */
class AClauseAboveASumIsReadAtTheFieldItIsAboutTest {

    private static final String THROUGH_A_SUM = """
            module g

            data Paging = { limit: Int }
            data A = { ...Paging, x: Int }
            data B = { ...Paging, y: Int }
            data Q = A | B

            data Holder = { q: Q }
                invariant fits = q.limit <= 10

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    /** The same clause where the field is under a record, which is what it has always done. */
    private static final String THROUGH_A_RECORD = THROUGH_A_SUM.replace("q: Q", "q: A");

    /**
     * The end the clause draws stands at the field under each case.
     *
     * <p>And it is the same end the clause draws where no sum is in the way, because a narrowing
     * does not change what a rule says.
     */
    @Test
    void theEndStandsUnderEachCase() {
        InputDomain sum = reading(THROUGH_A_SUM);
        InputDomain record = reading(THROUGH_A_RECORD);

        String underTheRecord = String.valueOf(
                record.at(TermPath.of("h").then("q").then("limit")).ownEnds());
        for (String each : List.of("A", "B")) {
            Position at = sum.at(TermPath.of("h").then("q").refine(caseNamed(sum,each)).then("limit"));
            assertNotNull(at, "the shared field is a position under the case");
            assertEquals(underTheRecord.replace("h.q.limit", "h.q@" + each + ".limit"),
                    String.valueOf(at.ownEnds()),
                    "the clause draws the end it draws, wherever the reading came through");
        }
    }

    /**
     * A field only one case declares is not reached from above.
     *
     * <p>The clause of the value above could not have named it, so nothing of that value's is read
     * there. A reading that walked outwards until something had a rule of the name would answer for
     * the same field of every other case.
     */
    @Test
    void aFieldOnlyOneCaseHasIsNotReachedFromAbove() {
        InputDomain sum = reading(THROUGH_A_SUM);
        Position own = sum.at(TermPath.of("h").then("q").refine(caseNamed(sum,"A")).then("x"));

        assertNotNull(own, "the case's own field is a position");
        assertNull(own.ownEnds() == null ? null : own.ownEnds().min(),
                "and nothing above bounds it");
    }

    /**
     * Two sums on the way and the clause is read at every pairing of their cases.
     *
     * <p>Each narrowing is crossed on its own, by the names that narrowing's cases share. Carried as
     * one rewrite of the whole name, whether the pairing is reached would be this compiler's answer
     * rather than the model's.
     */
    @Test
    void aClauseTwoSumsUpIsReadAtEveryPairing() {
        // The parameter is the outer sum, so that both narrowings fit inside the depth this reading
        // takes a product apart: a narrowing takes no level, so `deep` is two fields down however
        // many cases are named on the way.
        String nested = """
                module g

                data Inner = { deep: Int }
                data IA = { ...Inner, p: Int }
                data IB = { ...Inner, r: Int }
                data IS = IA | IB

                data Outer = { s: IS }
                data OA = { ...Outer, m: Int }
                data OB = { ...Outer, n: Int }
                data OS = OA | OB
                RULE

                data Ok

                behavior read : (q: OS) -> Ok
                """;

        assertEquals(List.of(), boundedIn(reading(nested.replace("RULE", ""))),
                "nothing bounds anything until a clause does");
        assertEquals(List.of("q@OA.s@IA.deep", "q@OA.s@IB.deep",
                        "q@OB.s@IA.deep", "q@OB.s@IB.deep"),
                boundedIn(reading(nested.replace("RULE",
                        "data Held = OS invariant deep = value.s.deep <= 10")
                        .replace("(q: OS)", "(q: Held)"))));
    }

    /**
     * Nothing crosses into what a sequence holds.
     *
     * <p>What a clause out here says about a list is written about the list, and an element is a
     * value with a declaration of its own. Crossed here as well, a rule about the container would be
     * read as a rule about each of the things in it.
     */
    @Test
    void nothingCrossesIntoWhatASequenceHolds() {
        InputDomain read = reading("""
                module g

                data Paging = { limit: Int }
                data A = { ...Paging, x: Int }
                data B = { ...Paging, y: Int }
                data Q = A | B

                data Holder = { qs: List<Q> }

                data Ok

                behavior read : (h: Holder) -> Ok
                """, "read");

        Position element = read.at(TermPath.of("h").then("qs").element());
        assertNotNull(element, "what the list holds is a position");
        assertTrue(read.reach().crossings().isEmpty()
                        || read.reach().crossings().stream()
                                .allMatch(each -> each.at().insideASequence()),
                "and any crossing under it is the sum's own, not the list's");
    }

    /**
     * A clause of the value above that this reading did not take in leaves the shared field short.
     *
     * <p>What a position is short of is asked of every reading that reaches it, and the value a case
     * was narrowed out of is one of them. Asked of the case alone, a field the value above wrote an
     * unread clause about came back as one every rule of which had been read.
     */
    @Test
    void aClauseAboveThisReadingDidNotTakeInLeavesTheFieldShort() {
        String model = """
                module g

                data Paging = { limit: Int }
                data A = { ...Paging, x: Int }
                data B = { ...Paging, y: Int }
                data Q = A | B

                data Floor = Int invariant atLeastOne = value >= 1

                data Holder = { q: HELD, floor: Floor }
                    invariant loose = q.limit >= floor + 1
                    invariant tight = q.limit >= floor + 5

                data Ok

                behavior read : (h: Holder) -> Ok
                """;
        InputDomain sum = reading(model.replace("HELD", "Q"));

        for (String each : List.of("A", "B")) {
            Position at = sum.at(TermPath.of("h").then("q")
                    .refine(caseNamed(sum, each)).then("limit"));
            assertFalse(at.rulesLeftUnread().isEmpty(),
                    () -> "the clause of `Holder` about this field went unread, and the field says "
                            + "so under case " + each);
        }
        assertFalse(reading(model.replace("HELD", "A"))
                        .at(TermPath.of("h").then("q").then("limit")).rulesLeftUnread().isEmpty(),
                "which is what the same clause leaves where no sum is in the way");
    }

    /**
     * A question the value above raised about the shared field is raised at each case.
     *
     * <p>A row is written under one case, so a question about what may stand at that field is a
     * question at every position the field stands at. Asked of the case's own rules alone, the
     * question the value above raised was one nobody was waiting on.
     */
    @Test
    void aQuestionRaisedAboveIsRaisedAtEachCase() {
        InputDomain read = reading("""
                module g

                data Code = String invariant shaped = String.length(value) >= 2
                data Paging = { code: Code }
                data A = { ...Paging, x: Int }
                data B = { ...Paging, y: Int }
                data Q = A | B

                data Holder = { q: Q }
                    invariant notBlank = q.code /= Code("zz")

                data Ok

                behavior read : (h: Holder) -> Ok
                """);

        for (String each : List.of("A", "B")) {
            Position at = read.at(TermPath.of("h").then("q")
                    .refine(caseNamed(read, each)).then("code"));
            assertEquals(1, at.unansweredQuestions().size(),
                    () -> "the question `Holder` raised stands at the field under case " + each);
        }
    }

    /** Every position something puts a ceiling on, spelled the way a report names it. */
    private static List<String> boundedIn(InputDomain read) {
        return read.positions().stream()
                .filter(each -> each.ownEnds() != null && each.ownEnds().max() != null)
                .map(each -> each.path().toString()).toList();
    }

    /** The narrowing that names this case of the sum the parameter or its field holds. */
    private static Refinement caseNamed(InputDomain read, String name) {
        for (Case each : read.at(TermPath.of("h").then("q")).obligationCases()) {
            if (each instanceof Case.SumCase one && one.leaf().name().equals(name)) {
                return Refinement.sumCase(one.leaf());
            }
        }
        throw new IllegalStateException("no case named " + name);
    }

    private static InputDomain reading(String source) {
        return reading(source, "read");
    }

    private static InputDomain reading(String source, String behavior) {
        Compilation compilation =
                Compilation.ofSources(List.of(source), souther.compiler.meta.ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals(behavior)).findFirst().orElseThrow();
        return InputDomain.of(spec, sigs.get(behavior), symbols, ReadAs.THE_COMPILATION_DOES);
    }
}
