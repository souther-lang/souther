package souther.compiler.core;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two expressions are one value where they read one name, or one field off one value, wherever each
 * of them was written.
 */
class TwoReadsOfOneValueAreOneValueWhereverTheyAreWrittenTest {

    private static final BindingId VALUE = new BindingId(new BindingOwner.OfValue("demo", "v"), 0);
    private static final BindingId OTHER = new BindingId(new BindingOwner.OfValue("demo", "v"), 1);

    private static Core read(BindingId binding, int column) {
        return new Core.Read("value", binding, Type.STRING, new SourcePos(1, column));
    }

    private static Core field(Core target, String name, int column) {
        return new Core.FieldAccess(target, name, Type.STRING, new SourcePos(1, column));
    }

    @Test
    void twoReadsOfOneNameAtTwoPlacesAreOneValue() {
        assertTrue(Core.sameValue(read(VALUE, 3), read(VALUE, 30)));
    }

    @Test
    void readsOfTwoNamesAreTwoValuesHoweverTheyAreSpelled() {
        assertFalse(Core.sameValue(read(VALUE, 3), read(OTHER, 3)));
    }

    @Test
    void oneFieldOffOneValueIsOneValueAndAnotherFieldIsNot() {
        assertTrue(Core.sameValue(field(read(VALUE, 3), "code", 9),
                field(read(VALUE, 30), "code", 36)));
        assertFalse(Core.sameValue(field(read(VALUE, 3), "code", 9),
                field(read(VALUE, 30), "name", 36)));
        assertFalse(Core.sameValue(field(read(VALUE, 3), "code", 9),
                field(read(OTHER, 30), "code", 36)));
    }

    /** A value and a field of it are two things, which is not something either spelling decides. */
    @Test
    void aValueAndAFieldOfItAreTwoValues() {
        assertFalse(Core.sameValue(read(VALUE, 3), field(read(VALUE, 3), "code", 9)));
    }
}
