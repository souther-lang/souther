package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a closure's answer is read as turns on what the reading proves of it — where in the element
 * it stands, that answers are equal where the element's values are, or that it is the element
 * itself — and not on how the answer was written: directly, through a {@code let}, or through a
 * name.
 *
 * <p>Held here rather than through a model, because a value standing as a wider type is the
 * checker's to place and no model written today puts one under a key; what is held is that the
 * reading refuses it wherever it stands.
 */
class WhatAnAnswerIsReadAsTurnsOnWhatTheReadingProvesTest {

    private static final SourcePos POS = new SourcePos(0, 0);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("example", "f");
    private static final BindingId ELEMENT = new BindingId(OWNER, 0);
    private static final BindingId NAME = new BindingId(OWNER, 1);
    private static final TypeKey LABEL_KEY = new TypeKey("example", "Label");
    private static final TypeSymbol.AtModule LABEL = TypeSymbols.declared(LABEL_KEY);
    private static final TypeSymbol.AtModule ISSUE =
            TypeSymbols.declared(new TypeKey("example", "Issue"));
    private static final DeclarationNewtypes NEWTYPES = LABEL_KEY::equals;

    private static final Core.Read THE_ELEMENT = new Core.Read("i", ELEMENT, Type.ref(ISSUE), POS);

    private static final Core LABEL_OF_IT =
            new Core.FieldAccess(THE_ELEMENT, "label", Type.STRING, POS);

    private static Core.Construct wearing(Core value) {
        return new Core.Construct(LABEL, List.of(new Core.FieldValue("value", value, POS)),
                Type.ref(LABEL), POS);
    }

    private static Core widened(Core value) {
        return new Core.Widen(value, Type.ref(TypeSymbols.declared(
                new TypeKey("example", "Wider"))));
    }

    /** {@code value} as the answer itself, as the body of a {@code let}, and as what a name the
     *  answer reads holds. */
    private record Written(Core answer, Map<BindingId, Core> held) { }

    private static List<Written> everyWayOfWriting(Core value) {
        return List.of(new Written(value, Map.of()),
                new Written(new Core.LetIn(new Core.Binder("key", NAME), value.type(), value,
                        new Core.Read("key", NAME, value.type(), POS), value.type(), POS),
                        Map.of(NAME, value)),
                new Written(new Core.Read("key", NAME, value.type(), POS), Map.of(NAME, value)));
    }

    private static <T> void readAlikeHoweverWritten(Core value, Function<Written, T> read,
                                                    T expected) {
        for (Written written : everyWayOfWriting(value)) {
            assertEquals(expected, read.apply(written), () -> "read of " + written);
        }
    }

    private static final Function<Written, OnePerElement.Answered> AS_A_KEY = written ->
            ElementProjection.readAsAKey(written.answer(), ELEMENT, written.held(), NEWTYPES);

    private static final Function<Written, Boolean> ITSELF = written ->
            ElementProjection.isTheElementItself(written.answer(), ELEMENT, written.held(),
                    NEWTYPES);

    private static final Function<Written, ElementProjection> A_PLACE = written ->
            ElementProjection.read(written.answer(), ELEMENT, written.held(), NEWTYPES);

    private static final ElementProjection THE_LABEL = ElementProjection.ofFields(List.of("label"));

    @Test
    void aNewtypeWearingAPlaceIsThatKeyWrappedHoweverItIsWritten() {
        readAlikeHoweverWritten(wearing(LABEL_OF_IT), AS_A_KEY,
                new OnePerElement.Answered(THE_LABEL, true));
    }

    @Test
    void aPlaceIsThatKeyHoweverItIsWritten() {
        readAlikeHoweverWritten(LABEL_OF_IT, AS_A_KEY,
                new OnePerElement.Answered(THE_LABEL, false));
    }

    /** A value standing as a wider type is no key however it is written, and where it stands
     *  is still where it stands. */
    @Test
    void aValueStandingWiderIsNoKeyHoweverItIsWritten() {
        readAlikeHoweverWritten(widened(LABEL_OF_IT), AS_A_KEY, null);
        readAlikeHoweverWritten(widened(LABEL_OF_IT), A_PLACE, THE_LABEL);
    }

    /** A newtype stands nowhere a place does: the reading of a place does not read through it. */
    @Test
    void aNewtypeIsNoPlace() {
        readAlikeHoweverWritten(wearing(LABEL_OF_IT), A_PLACE, null);
    }

    @Test
    void theElementIsItselfHoweverItIsWritten() {
        readAlikeHoweverWritten(THE_ELEMENT, ITSELF, true);
    }

    /** A field of the element, a newtype wearing it and the element standing as a wider type are
     *  each another value, however written. */
    @Test
    void whatIsMadeOfTheElementIsNotItself() {
        for (Core other : List.of(LABEL_OF_IT, wearing(THE_ELEMENT), widened(THE_ELEMENT))) {
            readAlikeHoweverWritten(other, ITSELF, false);
        }
    }

    /** A newtype's {@code value} is no step of a place, and still another value than the one it
     *  is read off. */
    @Test
    void aNewtypesValueIsNotTheNewtype() {
        Core.Read label = new Core.Read("l", ELEMENT, Type.ref(LABEL), POS);
        Core value = new Core.FieldAccess(label, "value", Type.STRING, POS);
        assertEquals(new ElementProjection(List.of()),
                ElementProjection.read(value, ELEMENT, Map.of(), NEWTYPES));
        assertFalse(ElementProjection.isTheElementItself(value, ELEMENT, Map.of(), NEWTYPES));
        assertTrue(ElementProjection.isTheElementItself(label, ELEMENT, Map.of(), NEWTYPES));
    }

    /** A field read back out of a construction is the value it was given, which is the element
     *  where the element was given. */
    @Test
    void aFieldOfAConstructionGivenTheElementIsTheElement() {
        Core.Construct made = new Core.Construct(ISSUE, List.of(new Core.FieldValue("of",
                THE_ELEMENT, POS)), Type.ref(ISSUE), POS);
        assertTrue(ElementProjection.isTheElementItself(
                new Core.FieldAccess(made, "of", Type.ref(ISSUE), POS), ELEMENT, Map.of(),
                NEWTYPES));
        assertNull(ElementProjection.readAsAKey(new Core.Str("x", Type.STRING, POS), ELEMENT,
                Map.of(), NEWTYPES));
    }
}
