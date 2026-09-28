package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.program.CheckedAlternativesForm;

import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A discriminated form cannot be made with the tag and a wrapped case's representation under one key.
 *
 * <p>A wrapped case writes both into one object, so such a form would put the representation where
 * the tag was and be read back by no decoder. The form a derivation settles never has this shape; what
 * is held here is that no one can build it, in the settled form or in its projection to the checked
 * program.
 */
class ADiscriminatedFormNeverPutsTwoThingsUnderOneKeyTest {

    @Test
    void theSettledFormRefusesOneKeyForBoth() {
        assertThrows(IllegalArgumentException.class,
                () -> new Boundary.Representation.Discriminated("value", "value"));
    }

    @Test
    void theCheckedProgramsFormRefusesOneKeyForBoth() {
        assertThrows(IllegalArgumentException.class,
                () -> new CheckedAlternativesForm.Discriminated("value", "value"));
    }
}
