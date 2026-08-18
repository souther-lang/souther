package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * What a value was written as is found by following what its name was given, and not by remembering
 * it beside the name.
 *
 * <p>A name is what it was given, so the text behind it is however many names away it was written —
 * which the walk already records, one binding at a time. Kept beside the denotation as well, the same
 * fact was held twice: once as what the binding stands for and once as the text a reading of it
 * folded, and the two had to be made to agree at every place a binding is entered.
 *
 * <p>Followed by what a name was given and not by what it denotes. A binding is what it was given
 * whatever kind of thing that is, so the rule is one rule — a {@code match} arm opening a value
 * written into the source opens that written value, and it is written there for the same reason the
 * name it was given is.
 */
class WhatWasWrittenIsFoundByFollowingWhatANameWasGivenTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "f");
    private static final ValueName.Behavior FIND = new ValueName.Behavior("demo", "findIt");
    private static final TypeSymbol FOUND = TypeSymbols.declared(new TypeKey("demo", "Found"));

    private final Hir.Binders binders = new Hir.Binders(OWNER);
    private final PathEngine engine =
            new PathEngine(Symbols.none(), Map.of(), Terms.Of.THE_DISCHARGE_TREE);

    @Test
    void aNameGivenTextIsThatText() {
        Core three = new Core.Int(3, Type.INT, POS);
        Hir.Binder a = binders.binder("a", POS);
        Denotations at = given(a, three, Denotations.none());

        assertSame(three, Terms.writtenValue(read(a), at));
    }

    /** However many names away. Each link records what it was given, so the text is at the end of the
     * chain and no link has to carry it. */
    @Test
    void aNameGivenANameGivenTextIsThatTextToo() {
        Core three = new Core.Int(3, Type.INT, POS);
        Hir.Binder a = binders.binder("a", POS);
        Hir.Binder b = binders.binder("b", POS);
        Hir.Binder c = binders.binder("c", POS);
        Denotations at = given(a, three, Denotations.none());
        at = given(b, read(a), at);
        at = given(c, read(b), at);

        assertSame(three, Terms.writtenValue(read(c), at));
    }

    /** A place stands for no value the walk reached, so there is no text behind it. */
    @Test
    void aPlaceWasGivenNothingSoItWasWrittenAsNothing() {
        Hir.Binder x = binders.binder("x", POS);
        Denotations at = engine.enter(Terms.read(x, Type.INT, POS), Known.top(),
                Denotations.none()).at();

        assertNull(Terms.writtenValue(read(x), at));
    }

    /** An arm opening a value written into the source opens that written value: the arm's name was
     * given the scrutinee, and following what a name was given is the whole of the rule. */
    @Test
    void anArmOpeningWrittenTextOpensThatText() {
        Core written = new Core.Construct(FOUND, List.of(), Type.ref(FOUND), POS);
        Hir.Binder x = binders.binder("x", POS);

        Denotations at = engine.enteringArm(
                arm(new Core.ResolvedPattern.Single(CaseSelector.direct(FOUND)), x),
                written, Known.top(), Denotations.none()).at();

        assertSame(written, Terms.writtenValue(read(x), at));
    }

    /** And an arm opening an answer opens nothing written, however the arm was entered. */
    @Test
    void anArmOpeningAnAnswerOpensNoText() {
        Core answer = new Core.Call(ReachName.of(FIND, "findIt", "demo"), FIND, List.of(),
                Type.ref(FOUND), POS);
        Hir.Binder x = binders.binder("x", POS);

        Denotations at = engine.enteringArm(
                arm(new Core.ResolvedPattern.Single(CaseSelector.direct(FOUND)), x),
                answer, Known.top(), Denotations.none()).at();

        assertNull(Terms.writtenValue(read(x), at));
    }

    /** A name given itself is a chain with no end, and following it is still an answer. Nothing the
     * walk records is one, but the following is written to end whatever it is handed. */
    @Test
    @Timeout(5)
    void aNameGivenItselfIsFollowedToNothing() {
        Hir.Binder a = binders.binder("a", POS);
        Hir.Binder b = binders.binder("b", POS);
        Denotations at = Denotations.none()
                .binding(a.id(), read(b), engine.terms().placeSubject(a.id()),
                        new Denotes.Nothing())
                .binding(b.id(), read(a), engine.terms().placeSubject(b.id()),
                        new Denotes.Nothing());

        assertNull(Terms.writtenValue(read(a), at));
    }

    /** What the check reads it for: a written value folds where it is written and where it is bound
     * alike, so a name given text is that text at the construction it is handed to. */
    @Test
    void aNameGivenTextIsWrittenWhereverItIsRead() {
        Core three = new Core.Int(3, Type.INT, POS);
        Hir.Binder a = binders.binder("a", POS);
        Denotations at = given(a, three, Denotations.none());

        assertEquals(engine.terms().denotationOf(three, Denotations.none()).getClass(),
                engine.terms().denotationOf(read(a), at).getClass(),
                "the text and the name it was given mean the same thing here");
    }

    private Denotations given(Hir.Binder binder, Core value, Denotations at) {
        return engine.bindLet(new Core.LetIn(binder, value,
                new Core.Read(binder.name(), binder.id(), value.type(), POS), value.type(), POS),
                Known.top(), at).at();
    }

    private Core.Case arm(Core.ResolvedPattern pattern, Hir.Binder binder) {
        return new Core.Case(pattern, binder, new Core.Read(binder.name(), binder.id(),
                pattern.bindType(), POS), POS);
    }

    private static Core read(Hir.Binder binder) {
        return new Core.Read(binder.name(), binder.id(), Type.INT, POS);
    }
}
