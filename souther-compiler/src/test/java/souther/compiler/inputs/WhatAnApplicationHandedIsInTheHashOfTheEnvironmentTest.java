package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ElementBindings;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * What an application of a closure handed its parameter is part of the hash of the environment, as
 * it is of what the environment equals: two applications handing one name different values are
 * two hashes, and environments that hand the same values are one, however they came to.
 *
 * <p>An environment keys the readings kept by it. Hashed by the names handed alone, every
 * application of a closure over the values written out lands on one hash, and each reading kept
 * by one of them is told from the others by walking the values handed.
 */
class WhatAnApplicationHandedIsInTheHashOfTheEnvironmentTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "go");
    private static final BindingId EACH = new BindingId(OWNER, 0);
    private static final BindingId OTHER = new BindingId(OWNER, 1);

    private static BindingEnvironment nothingHanded() {
        return new BindingEnvironment(Map.of(), Map.of(), ElementBindings.NONE,
                ValueDefinitions.NONE, false);
    }

    private static Core written(long value) {
        return new Core.Int(value, Type.INT, POS);
    }

    @Test
    void twoApplicationsHandingDifferentValuesAreTwoHashes() {
        BindingEnvironment one = nothingHanded().handing(EACH, written(1));
        BindingEnvironment two = nothingHanded().handing(EACH, written(2));

        assertNotEquals(one, two);
        assertNotEquals(one.hashCode(), two.hashCode());
    }

    @Test
    void theSameValuesHandedAreOneEnvironmentHoweverTheyCameTo() {
        BindingEnvironment direct = nothingHanded().handing(EACH, written(2))
                .handing(OTHER, written(3));
        BindingEnvironment reordered = nothingHanded().handing(OTHER, written(3))
                .handing(EACH, written(2));
        BindingEnvironment replaced = nothingHanded().handing(EACH, written(1))
                .handing(OTHER, written(3)).handing(EACH, written(2));

        assertEquals(direct, reordered);
        assertEquals(direct.hashCode(), reordered.hashCode());
        assertEquals(direct, replaced);
        assertEquals(direct.hashCode(), replaced.hashCode());
    }
}
