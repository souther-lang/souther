package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The parameters a relation reads a place under are those of every place its numbers are read
 * off ({@link UndividedByARelation#parametersRead}), and not of where each number is filed: how
 * many times a key occurs in a run is filed under the run and read off the key as well, which may
 * stand in another parameter.
 */
class WhatARelationIsReadOffIsEveryPlaceItsNumbersAreReadOffTest {

    private static final TermPath RUN = TermPath.of("xs").element().element();
    private static final TermPath KEY = TermPath.of("k");
    private static final TermPath OTHER = TermPath.of("o");

    @Test
    void aCountOfAKeysOccurrencesReadsTheParameterTheKeyIsIn() {
        NumericTerm occurrences =
                NumericTerm.OccurrencesOfAKey.of(new RunSource.FlattenedOccurrences(RUN), KEY);
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(occurrences, ExactRatio.ONE);
        coefs.put(new NumericTerm.ValueOf(OTHER), ExactRatio.ONE.negated());
        UndividedByARelation relation = UndividedByARelation.ofTheInputsNumbers(
                new LinearForm<>(ExactRatio.ZERO, coefs), ExactRatio.ZERO, Rel.GE);

        assertEquals(Optional.of(Set.of("xs", "k", "o")), relation.parametersRead());
    }
}
