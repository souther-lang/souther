package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.Text;

import java.util.Arrays;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every kind of statement a condition can mean, handed to what a path knows past it, is known or
 * meets the edge of what a path knows — and is never said to be a meaning this compiler did not
 * read, unless a part of it was one.
 *
 * <p>The edges are the path's own: what it knows is relations of numbers, truths and what every
 * element was written to meet, about the places of the tree it walks. So a limit of what a row is
 * written in coming out of here would send an author to the wrong reader, as a "not read" for a
 * statement read to the end would pass off a limit of this reader as one of the reading.
 *
 * <p>Handed with no places, so every statement about a position meets the edge that the tree it
 * is walked over reads no place for it, and the rest meet the edge of their own kind; which of
 * them a path does take in, where it reads the places, is said by the tests of each.
 */
class EveryPropositionAPathIsHandedIsKnownOrMeetsTheEdgeOfWhatItKnowsTest {

    /** Where what a path knows stops, and nothing of what a row is written in. */
    private static final Set<WhyNotTaken.DomainLimit> A_PATHS_EDGES =
            EnumSet.allOf(WhyNotTaken.DomainLimit.class).stream()
                    .filter(each -> each.domain()
                            == WhyNotTaken.DomainLimit.Domain.WHAT_A_PATH_KNOWS)
                    .collect(Collectors.toCollection(
                            () -> EnumSet.noneOf(WhyNotTaken.DomainLimit.class)));

    @Test
    void everyKindOfStatementHasASampleHere() {
        Set<Class<?>> sampled = new LinkedHashSet<>();
        samples().values().forEach(each -> sampled.add(each.getClass()));
        assertEquals(new LinkedHashSet<>(Arrays.asList(Proposition.class.getPermittedSubclasses())),
                sampled, "a kind of statement no path below was handed");
    }

    @Test
    void whatAPathDoesNotTakeInIsAnEdgeOfWhatItKnows() {
        samples().forEach((name, stated) -> {
            boolean readToTheEnd = Proposition.stopsIn(stated).isEmpty();
            for (boolean positive : List.of(true, false)) {
                for (WhyNotTaken why : notTaken(stated, positive)) {
                    switch (why) {
                        case WhyNotTaken.OutsideDomain(var limit) ->
                                assertTrue(A_PATHS_EDGES.contains(limit),
                                        () -> name + " coming out " + positive + " met " + limit
                                                + ", which is no edge of what a path knows");
                        case WhyNotTaken.MeaningUnread _ -> assertTrue(!readToTheEnd,
                                () -> name + " coming out " + positive
                                        + " was read to the end: " + why);
                    }
                }
            }
        });
    }

    private static List<WhyNotTaken> notTaken(Proposition stated, boolean positive) {
        return MeaningAssumptions.assumed(stated, positive, Known.top(), null,
                MeaningAssumptions.InputPlaces.NONE, null).notTaken();
    }

    /** One statement of each kind, each read to the end but the one that says so. */
    private static Map<String, Proposition> samples() {
        Proposition above = new Proposition.Compared(new Relation.Affine(
                LinearForm.<Quantity>atomMinusConstant(
                        new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("n"))),
                        ExactRatio.of(5)), Rel.GT), true);
        Proposition truth = new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("b")),
                true);
        Proposition element = new Proposition.Compared(new Relation.Affine(
                LinearForm.<Quantity>atom(new DecisionAtom.OfTheInput(
                        new NumericTerm.ValueOf(TermPath.of("xs").element()))), Rel.GT), true);
        TermPath optional = TermPath.of("h").then("o");
        Rel before = Rel.LT.orItsDenial();
        Map<String, Proposition> out = new LinkedHashMap<>();
        out.put("always", new Proposition.Always(true));
        out.put("a relation of numbers", above);
        out.put("a place on an order", new Proposition.Compared(new Relation.Ordered(
                new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("s"))),
                Text.of("M"), before), before == Rel.LT));
        out.put("a truth", truth);
        out.put("a case", new Proposition.InCases(new DecisionSubject.AnInput(optional),
                CasesLeft.of(Refinement.of(new Case.Presence(true))), true));
        out.put("a value being there",
                new Proposition.Present(new DecisionSubject.AnInput(optional), true));
        out.put("two values being one", new Proposition.SameValue(
                new DecisionSubject.AnInput(TermPath.of("n")),
                new DecisionSubject.AnInput(TermPath.of("s")), true));
        out.put("both", new Proposition.All(List.of(above, truth)));
        out.put("either", new Proposition.Any(List.of(above, truth)));
        out.put("some element", new Proposition.Some(TermPath.of("xs"), element, true));
        out.put("on some application", new Proposition.OnAnApplication(List.of(above, truth)));
        out.put("unread", new Proposition.Unread(Optional.empty(), 0,
                new WhyUnread.NotMetByTheReading(), false, true));
        return out;
    }
}
