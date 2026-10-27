package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.partition.UndividedByARelation.StringsAPartnerCanHold;
import souther.compiler.partition.UndividedByARelation.WhatItLeaves;
import souther.compiler.values.ValueSet;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The positions a relation parts by what their partner can hold come back in the order they were
 * said in, which is the order of the relation's sides.
 *
 * <p>Whoever files a reading for each of them numbers the readings in the order it is handed them,
 * so an order that depends on the keys' hashes and on the run numbers the same reading differently
 * from one run to the next. An unordered copy keeps the pairs and loses that, and which of two
 * positions comes first then differs between runs of the same model. Many pairs are asked, since
 * one pair of keys comes out the same on every run of one machine.
 */
class WhatARelationPartsByWhatItsPartnerCanHoldIsKeptInTheOrderOfItsSidesTest {

    private static final int MANY = 40;

    private static Map<NumericTerm.FromOnePosition, StringsAPartnerCanHold> said(int pair) {
        Map<NumericTerm.FromOnePosition, StringsAPartnerCanHold> out = new LinkedHashMap<>();
        for (int side = 0; side < 2; side++) {
            out.put(new NumericTerm.ValueOf(TermPath.of("p" + pair + "s" + side)),
                    new StringsAPartnerCanHold(ValueSet.ANY, "partner" + side));
        }
        return out;
    }

    @Test
    void thePositionsComeBackInTheOrderTheyWereSaidIn() {
        for (int pair = 0; pair < MANY; pair++) {
            Map<NumericTerm.FromOnePosition, StringsAPartnerCanHold> said = said(pair);
            WhatItLeaves leaves = new WhatItLeaves(Set.of(), Map.of(), true, Set.of(), Set.of(),
                    said);

            assertEquals(List.copyOf(said.keySet()), List.copyOf(leaves.partnered().keySet()),
                    "pair " + pair);
        }
    }

    @Test
    void whatIsKeptAlongBothWaysIsInTheSameOrder() {
        for (int pair = 0; pair < MANY; pair++) {
            Map<NumericTerm.FromOnePosition, StringsAPartnerCanHold> said = said(pair);
            WhatItLeaves one = new WhatItLeaves(Set.of(), Map.of(), true, Set.of(), Set.of(), said);

            assertEquals(List.copyOf(said.keySet()),
                    List.copyOf(one.alongBoth(one).partnered().keySet()), "pair " + pair);
        }
    }
}
