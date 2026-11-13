package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.ValueIdentity;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * That some element of a container is a value held outside it is a search for that value, whether
 * the statement says the two are one or says it as the comparison of the element with the value:
 * the search ends where an equal element is found, which no other statement over the same two
 * places says.
 *
 * <p>So only the equality of the element with the value, stated of some element, is held for a
 * search, and every near thing is not: the two weighed otherwise, the two not one value, the
 * statement denied, no element of the container being it, and a place worked out of another.
 */
class AnElementHeldEqualToAValueIsASearchOnlyWhereTheStatementSaysSoTest {

    private static final TermPath LIST = TermPath.of("emails");

    private static final TermPath ELEMENT = LIST.element();

    private static final TermPath VALUE = TermPath.of("email");

    private static final DecisionSubject CONTAINER = new DecisionSubject.AnInput(LIST);

    private static Quantity at(TermPath place) {
        return new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(place),
                ValueIdentity.AT_THE_POSITION);
    }

    private static LinearForm<Quantity> form(TermPath first, long firstWeight, TermPath second,
                                             long secondWeight) {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(at(first), ExactRatio.of(firstWeight));
        coefs.put(at(second), ExactRatio.of(secondWeight));
        return new LinearForm<>(ExactRatio.ZERO, coefs);
    }

    private static UndividedByARelation.Search searchedAs(LinearForm<Quantity> form, Rel rel,
                                                         boolean statedHolds,
                                                         boolean someHolds) {
        Proposition.Compared compared =
                new Proposition.Compared(new Relation.Affine(form, rel), statedHolds);
        return UndividedByARelation.ofAForm(form, rel)
                .searchedBy(new Proposition.Some(CONTAINER, compared, someHolds)).search();
    }

    @Test
    void theEqualityOfTheElementWithTheValueIsASearchForTheValue() {
        UndividedByARelation.Search search =
                searchedAs(form(VALUE, 1, ELEMENT, -1), Rel.EQ, true, true);
        assertNotNull(search);
        assertEquals(FilingCoordinate.at(ELEMENT), search.searched());
        assertEquals(FilingCoordinate.at(VALUE), search.probe());
    }

    @Test
    void nothingNearItIs() {
        LinearForm<Quantity> equal = form(VALUE, 1, ELEMENT, -1);
        assertNull(searchedAs(equal, Rel.EQ, false, true), "the comparison denied");
        assertNull(searchedAs(equal, Rel.EQ, true, false),
                "no element of the container being it");
        assertNull(searchedAs(equal, Rel.GT, true, true), "the value above the element");
        assertNull(searchedAs(form(VALUE, 2, ELEMENT, -1), Rel.EQ, true, true),
                "the two weighed otherwise");
        assertNull(searchedAs(form(VALUE, 1, ELEMENT, 1), Rel.EQ, true, true),
                "the two summing to nought");
        assertNull(searchedAs(form(VALUE, 1, TermPath.of("other"), -1), Rel.EQ, true, true),
                "two places neither of which is an element of the container");
    }
}
