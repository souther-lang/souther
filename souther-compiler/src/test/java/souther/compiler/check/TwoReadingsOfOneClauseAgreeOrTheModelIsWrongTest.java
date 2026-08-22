package souther.compiler.check;

import souther.compiler.source.SourceId;

import souther.compiler.diag.DiagnosticPlace;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.SourceProvenance;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

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
     * The three properties, held over readings the model can actually produce.
     *
     * <p>Which is what settles them. Nothing here picks between two readings, so there is no rule
     * whose preference could depend on the order or the grouping — two readings of one clause say
     * the same thing about it, and a pair that does not is refused whichever way round it is asked.
     * The version before this preferred the reading that could point somewhere, and was associative
     * without being commutative, then commutative without being associative.
     */
    @Test
    void mergingIsCommutativeAssociativeAndIdempotent() {
        Clause one = clause(FIRST, "ordered", at("model.sou", 8));
        Clause two = clause(FIRST, "ordered", at("model.sou", 8));
        Clause three = clause(FIRST, "ordered", at("model.sou", 8));

        assertEquals(Clause.merge(one, two), Clause.merge(two, one));
        assertEquals(Clause.merge(Clause.merge(one, two), three),
                Clause.merge(one, Clause.merge(two, three)));
        assertEquals(one, Clause.merge(one, one));
    }

    /**
     * Two readings that reached the clause by two names are one reading.
     *
     * <p>Where the clause is written is a fact about the declaration and the same for every reading;
     * the name a reading reached the code by is a fact about that reading, and two readings of one
     * clause reach it by two names as easily as one. Carried into what a clause holds, the two are
     * different values and the merge has a pair to choose between — which is a first-wins union
     * whichever rule it chooses by. A clause takes the declaration's own form, so there is nothing
     * left to differ in.
     */
    @Test
    void twoReadingsThatReachedTheSameClauseByTwoNamesAreOneReading() {
        Clause viaOne = clause(FIRST, "ordered", new DiagnosticPlace.Unavailable(
                new SourceProvenance.APublishedModule("lib.rule", "A.Code")));
        Clause viaTwo = clause(FIRST, "ordered", new DiagnosticPlace.Unavailable(
                new SourceProvenance.APublishedModule("lib.rule", "B.Code")));

        assertEquals(viaOne, viaTwo, "a clause holds where it is written, not how it was reached");
        assertEquals(viaOne, Clause.merge(viaOne, viaTwo));
        assertEquals(viaOne, Clause.merge(viaTwo, viaOne));
    }

    private static final TypeSymbol BOUND = TypeSymbols.declared(new TypeKey("demo", "Bound"));
    private static final TypeSymbol OTHER = TypeSymbols.declared(new TypeKey("demo", "Other"));

    private static final Clause.Id FIRST = new Clause.Id(BOUND, 0);
    private static final Clause.Id SECOND = new Clause.Id(BOUND, 1);

    private static DiagnosticPlace at(String sourceId, int line) {
        return DiagnosticPlace.of(new Region(new SourcePos(line, 5, new SourceId(sourceId)),
                new SourcePos(line, 30, new SourceId(sourceId))));
    }

    /** A clause of a module this compile holds no file for: written somewhere, quotable nowhere. */
    private static DiagnosticPlace outOfSight() {
        return new DiagnosticPlace.Unavailable(
                new SourceProvenance.APublishedModule("lib.rule"));
    }

    private static Clause clause(Clause.Id id, String name, DiagnosticPlace at) {
        return new Clause(id, Optional.ofNullable(name).map(ClauseName::new), at);
    }

    // --- what may not differ ----------------------------------------------------------------

    /**
     * A reading that can quote the clause and one that cannot are two answers about where one
     * clause is written, and one of them is wrong.
     *
     * <p>This used to be the tolerance the merge was built around, and it had a reason: a reading
     * that could not point was an absent value, so which representation a clause was reached
     * through decided how much a reading knew. It decides nothing now. A clause is quotable or it is
     * out of sight because of the declaration it is on, and "no place at all" is not something a
     * reading can produce — so a pair like this is the compiler saying one declaration is in two
     * places. Measured over the whole suite before it was refused: no compile produces one.
     */
    @Test
    void aQuotableReadingAndAnUnquotableOneAreNotTwoReadingsOfOneClause() {
        Clause quotable = clause(FIRST, "ordered", at("model.sou", 8));
        Clause outOfSight = clause(FIRST, "ordered", outOfSight());

        assertThrows(Clause.NotOneClause.class, () -> Clause.merge(quotable, outOfSight));
        assertThrows(Clause.NotOneClause.class, () -> Clause.merge(outOfSight, quotable),
                "and the same the other way round, or the walk's order decides what is noticed");
    }

    @Test
    void twoReadingsThatKnowNothingStillKnowNothing() {
        Clause blind = clause(FIRST, "ordered", outOfSight());

        assertEquals(blind, Clause.merge(blind, blind));
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
