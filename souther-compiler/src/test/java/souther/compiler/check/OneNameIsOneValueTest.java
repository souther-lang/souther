package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A name the discharge check gives an atom is a name for one value.
 *
 * <p>Every relation the numeric domain records is recorded against a name, so two values under one
 * name is every relation about one of them read as a relation about the other. The kind of number
 * behind a name is what catches it: a whole number and a dense one are not the same value however
 * alike they are written.
 *
 * <p>Held here because the check is fail-open. A walk that falls over produces what a walk that found
 * nothing produces, so a contradiction inside the check would arrive as a behavior with no findings —
 * silence that reads as every invariant discharged. What this holds is that one failure is refused
 * rather than recorded: the check may be unable to answer for a program, and it may not disagree with
 * itself about its own names.
 */
class OneNameIsOneValueTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static BindingId binding() {
        return new BindingId(new BindingOwner.OfValue("demo", "f"), 0);
    }

    @Test
    void oneKeyIsRefusedASecondKindOfNumber() {
        Terms terms = new Terms(Symbols.none(), souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
        BindingId binding = binding();
        Denotations at = Denotations.none().location(binding, AsPlaces.of(binding), AsPlaces.term(binding));
        FactSubject whole = terms.atomOf(new Core.Read("n", binding, Type.INT, POS), at);
        assertNotNull(whole, "a location is an atom");
        Terms.OneTermTwoKinds refused = assertThrows(Terms.OneTermTwoKinds.class,
                () -> terms.atomOf(new Core.Read("n", binding, Type.DECIMAL, POS), at),
                "the same name, standing for a number spaced the other way");
        assertTrue(refused.getMessage().contains(whole.rendered()),
                "and it says which name: " + refused.getMessage());
    }

    /**
     * Two values one writing of them once ran together are two terms.
     *
     * <p>A term was a string built out of its parts' strings, and the punctuation the string used was
     * punctuation a value could hold: the one-element list below and the two-element one wrote the
     * same characters, so a guard about either discharged a clause about the other. What separates
     * them now is that neither is written at all — a term holds its parts, and a list of one is a
     * list of one whatever that one spells.
     */
    @Test
    void twoValuesThatOnceWroteOneNameAreTwoTerms() {
        Terms terms = new Terms(Symbols.none(), souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
        Denotations at = Denotations.none();
        Core.Str awkward = new Core.Str("a\", \"b", Type.STRING, POS);

        Term one = terms.bodyKey(new Core.ListLit(java.util.List.of(awkward),
                Type.list(Type.STRING), POS), at);
        Term two = terms.bodyKey(new Core.ListLit(java.util.List.of(
                new Core.Str("a", Type.STRING, POS), new Core.Str("b", Type.STRING, POS)),
                Type.list(Type.STRING), POS), at);

        assertNotNull(one);
        assertNotEquals(one, two, "a list of one element and a list of two are two values");
    }

    @Test
    void theCheckDoesNotSwallowItsOwnContradiction() {
        assertThrows(Terms.OneTermTwoKinds.class,
                () -> InvariantChecker.gaveUp("analyze",
                        new Terms.OneTermTwoKinds("atom `n` is DISCRETE and DENSE")),
                "recording it would leave a behavior looking like one with nothing to report");
    }

    @Test
    void andStillGivesUpOnAShapeItHasNoRuleFor() {
        assertDoesNotThrow(() -> InvariantChecker.gaveUp("analyze",
                        new IllegalStateException("something the walk has no rule for")),
                "which is what fail-open is for");
    }
}
