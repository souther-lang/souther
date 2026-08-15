package souther.compiler.check;

import souther.compiler.diag.DiagnosticPlace;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.SourceProvenance;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What two readings of one clause come to, and what they may not come to.
 *
 * <p>One construction is read once per branch of a conditional above it, and the two readings are
 * combined. They differ in what they could prove and not in what the declaration says, so the one
 * fact that may be in one and missing from the other is whether this compile can quote where the
 * clause was written. Everything else differing is the compiler having called two clauses one, or
 * one clause two, and answering that with a clause would report a declaration nobody wrote.
 *
 * <p>Commutative, associative and idempotent, because the order the walk combines branches in is not
 * something a reader should be able to see. A first-wins union reads as one of these until a clause
 * is reached by two paths that know different amounts, and then the warning points somewhere or
 * nowhere depending on which branch the walk read first.
 */
class TwoReadingsOfOneClauseAgreeOrTheModelIsWrongTest {

    /**
     * Associativity, held over the grouping that used to break it.
     *
     * <p>A reading that can point absorbs one that cannot. So a rule refusing a disagreement between
     * two unpointable readings finds it or not depending on which pair is merged first, and what
     * becomes order-dependent is not the answer but whether the compiler notices it contradicts
     * itself. Held here over the three readings that show it.
     */
    @org.junit.jupiter.api.Test
    void aGroupingDoesNotDecideWhetherTheReadingsAgree() {
        Clause known = clause(FIRST, "ordered", at("model.sou", 8));
        Clause fromA = clause(FIRST, "ordered", new DiagnosticPlace.Unavailable(
                new SourceProvenance.APublishedModule("lib.a")));
        Clause fromB = clause(FIRST, "ordered", new DiagnosticPlace.Unavailable(
                new SourceProvenance.APublishedModule("lib.b")));

        assertEquals(Clause.merge(Clause.merge(known, fromA), fromB),
                Clause.merge(known, Clause.merge(fromA, fromB)),
                "which pair is merged first is not something a reader should be able to see");
        assertEquals(known, Clause.merge(known, Clause.merge(fromA, fromB)),
                "and the reading that can point is what survives either way");
    }

    /**
     * Commutativity, held where the two readings differ only in how each of them got there.
     *
     * <p>Where the clause is written is a fact about the declaration and the same for every reading;
     * the name a reading reached the code by is a fact about that reading, and two readings of one
     * clause reach it by two names as easily as one. Carried into what a clause holds, the two are
     * different values and merging them answers differently each way round — a first-wins union
     * wearing the name of a join. A clause takes the declaration's own form, so there is nothing
     * left to differ in.
     */
    @org.junit.jupiter.api.Test
    void twoReadingsThatReachedTheSameClauseByTwoNamesAreOneReading() {
        Clause viaOne = clause(FIRST, "ordered", new DiagnosticPlace.Unavailable(
                new SourceProvenance.APublishedModule("lib.rule", "A.Code")));
        Clause viaTwo = clause(FIRST, "ordered", new DiagnosticPlace.Unavailable(
                new SourceProvenance.APublishedModule("lib.rule", "B.Code")));

        assertEquals(viaOne, viaTwo, "a clause holds where it is written, not how it was reached");
        assertEquals(Clause.merge(viaOne, viaTwo), Clause.merge(viaTwo, viaOne),
                "so which reading is asked first is not something a reader can see");
    }


    private static final TypeSymbol BOUND = TypeSymbols.declared(new TypeKey("demo", "Bound"));
    private static final TypeSymbol OTHER = TypeSymbols.declared(new TypeKey("demo", "Other"));

    private static final Clause.Id FIRST = new Clause.Id(BOUND, 0);
    private static final Clause.Id SECOND = new Clause.Id(BOUND, 1);

    private static DiagnosticPlace at(String sourceId, int line) {
        return DiagnosticPlace.of(new Region(new SourcePos(line, 5, sourceId),
                new SourcePos(line, 30, sourceId)));
    }

    /** A clause of a module this compile holds no file for: written somewhere, quotable nowhere. */
    private static DiagnosticPlace outOfSight() {
        return new DiagnosticPlace.Unavailable(
                new SourceProvenance.APublishedModule("lib.rule"));
    }

    private static Clause clause(Clause.Id id, String name, DiagnosticPlace at) {
        return new Clause(id, Optional.ofNullable(name).map(ClauseName::new), at);
    }

    // --- what may differ --------------------------------------------------------------------

    @Test
    void aReadingThatKnowsWhereTheClauseIsTellsTheOneThatDoesNot() {
        Clause knows = clause(FIRST, "ordered", at("model.sou", 8));
        Clause doesNot = clause(FIRST, "ordered", outOfSight());

        assertEquals(knows, Clause.merge(knows, doesNot));
        assertEquals(knows, Clause.merge(doesNot, knows),
                "and the same the other way round, or the walk's order decides");
    }

    @Test
    void twoReadingsThatKnowNothingStillKnowNothing() {
        Clause blind = clause(FIRST, "ordered", outOfSight());

        assertEquals(blind, Clause.merge(blind, blind));
    }

    // --- the algebra ------------------------------------------------------------------------

    @Test
    void mergingIsCommutativeAssociativeAndIdempotent() {
        Clause knows = clause(FIRST, "ordered", at("model.sou", 8));
        Clause blind = clause(FIRST, "ordered", outOfSight());
        Clause same = clause(FIRST, "ordered", at("model.sou", 8));

        for (List<Clause> order : List.of(List.of(knows, blind, same), List.of(blind, same, knows),
                List.of(same, knows, blind), List.of(blind, knows, same))) {
            assertEquals(knows,
                    Clause.merge(Clause.merge(order.get(0), order.get(1)), order.get(2)),
                    "left to right: " + order);
            assertEquals(knows,
                    Clause.merge(order.get(0), Clause.merge(order.get(1), order.get(2))),
                    "right to left: " + order);
        }
    }

    // --- what may not differ ----------------------------------------------------------------

    @Test
    void twoClausesAreNotMergedIntoOne() {
        assertThrows(Clause.NotOneClause.class, () -> Clause.merge(
                clause(FIRST, "ordered", outOfSight()),
                clause(SECOND, "ordered", outOfSight())));
        assertThrows(Clause.NotOneClause.class, () -> Clause.merge(
                clause(FIRST, "ordered", outOfSight()),
                clause(new Clause.Id(OTHER, 0), "ordered", outOfSight())));
    }

    /**
     * A name is what the declaration says, not what a reading found out, so one reading finding a
     * name where another found none is not a reading that knew more. It is the two of them reading
     * different declarations under one identity.
     */
    @Test
    void oneClauseIsNotNamedTwoWays() {
        assertThrows(Clause.NotOneClause.class, () -> Clause.merge(
                clause(FIRST, "ordered", outOfSight()),
                clause(FIRST, "lowNonNegative", outOfSight())));
        assertThrows(Clause.NotOneClause.class, () -> Clause.merge(
                clause(FIRST, "ordered", outOfSight()),
                clause(FIRST, null, outOfSight())));
        assertThrows(Clause.NotOneClause.class, () -> Clause.merge(
                clause(FIRST, null, outOfSight()),
                clause(FIRST, "ordered", outOfSight())));
    }

    /** Nor written in two places. Which of them is right is not a question with an answer here:
     *  either the ordinal or what carries a clause through a rewrite is wrong. */
    @Test
    void oneClauseIsNotWrittenInTwoPlaces() {
        assertThrows(Clause.NotOneClause.class, () -> Clause.merge(
                clause(FIRST, "ordered", at("model.sou", 8)),
                clause(FIRST, "ordered", at("model.sou", 20))));
        assertThrows(Clause.NotOneClause.class, () -> Clause.merge(
                clause(FIRST, "ordered", at("model.sou", 8)),
                clause(FIRST, "ordered", at("other.sou", 8))));
    }

    /**
     * And none of that is something the check may give up on. It swallows what a walk throws — an
     * analysis that fell over leaves the run-time check standing — so a disagreement thrown down
     * there would come out as a behavior with nothing to report, which is what a behavior whose
     * invariants all discharge comes out as.
     */
    @Test
    void aDisagreementIsNotSomethingTheCheckMayGiveUpOn() {
        Clause.NotOneClause disagreement = assertThrows(Clause.NotOneClause.class,
                () -> Clause.merge(clause(FIRST, "ordered", outOfSight()),
                        clause(FIRST, null, outOfSight())));

        assertThrows(Clause.NotOneClause.class,
                () -> InvariantChecker.gaveUp("a test", disagreement));
    }
}
