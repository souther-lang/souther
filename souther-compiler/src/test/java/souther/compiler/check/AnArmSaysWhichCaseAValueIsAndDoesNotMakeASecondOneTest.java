package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;
import souther.compiler.check.BehaviorContract.Guard;
import souther.compiler.check.BehaviorContract.RuleId;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Opening a value says which case it is. It does not produce a second value.
 *
 * <p>An arm naming one case of a declared sum, or several of them, binds what it was given — the
 * case's class is tested and the value read is that instance — so the arm's name and the scrutinee
 * are one value. Entered as a place of its own, that value had two subjects: everything the answer
 * guaranteed was filed under one and everything the arm knew under the other, with nothing relating
 * them. They agreed only because no program could reach a fact under one and read it under the other
 * (#824).
 *
 * <p>An optional's present carrier is the other case: what it binds stands under the optional and is
 * not the optional, so it is a value of its own and is introduced as one. The two are told apart by
 * what the pattern binds and not by what the arm looks like.
 */
class AnArmSaysWhichCaseAValueIsAndDoesNotMakeASecondOneTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "f");
    private static final ValueName.Behavior FIND = new ValueName.Behavior("demo", "findIt");
    private static final TypeSymbol FOUND = TypeSymbols.declared(new TypeKey("demo", "Found"));
    private static final TypeSymbol MISSING = TypeSymbols.declared(new TypeKey("demo", "Missing"));

    private static final TypeSymbol AN_INT = TypeSymbol.primitive("Int");

    private final Hir.Binders binders = new Hir.Binders(OWNER);
    private final PathEngine engine =
            new PathEngine(Symbols.none(), Map.of(), Terms.Of.THE_DISCHARGE_TREE, souther.compiler.query.ReadAs.THE_COMPILATION_DOES);

    @Test
    void anArmOverOneCaseIsAboutTheValueItOpened() {
        Core answer = answer();
        Hir.Binder x = binders.binder("x", POS);

        PathEngine.Entered in = engine.enteringArm(
                arm(new Core.ResolvedPattern.Single(CaseSelector.direct(FOUND)), x),
                answer, Known.top(), Denotations.none());

        FactSubject opened = in.at().subject(x.id());
        assertNotNull(opened, "an arm binds something to be known about");
        assertEquals(engine.terms().subjectOf(answer, Denotations.none()), opened,
                "the value the arm opened is the value it was given");
    }

    @Test
    void anArmOverSeveralCasesIsAboutTheValueItOpened() {
        Core answer = answer();
        Hir.Binder x = binders.binder("x", POS);

        PathEngine.Entered in = engine.enteringArm(
                arm(new Core.ResolvedPattern.AnyOf(
                        List.of(CaseSelector.direct(FOUND), CaseSelector.direct(MISSING)),
                        Type.ref(FOUND)), x),
                answer, Known.top(), Denotations.none());

        assertEquals(engine.terms().subjectOf(answer, Denotations.none()), in.at().subject(x.id()),
                "an arm naming several says the value is one of them, and it is still that value");
    }

    /** Two matches over one answer open one value, so a fact taken under either is about the same
     * subject. That is what a second subject per arm cost. */
    @Test
    void twoArmsOverOneAnswerOpenOneValue() {
        Core answer = answer();
        Hir.Binder first = binders.binder("a", POS);
        Hir.Binder second = binders.binder("b", POS);

        FactSubject one = engine.enteringArm(
                arm(new Core.ResolvedPattern.Single(CaseSelector.direct(FOUND)), first),
                answer, Known.top(), Denotations.none()).at().subject(first.id());
        FactSubject other = engine.enteringArm(
                arm(new Core.ResolvedPattern.Single(CaseSelector.direct(FOUND)), second),
                answer, Known.top(), Denotations.none()).at().subject(second.id());

        assertEquals(one, other);
    }

    /** What stands under a present optional is not the optional, and it is what that optional
     * holds — not a value the arm made up. */
    @Test
    void whatAnOptionalHoldsIsWhatThatOptionalHolds() {
        Core answer = optionalAnswer();
        Hir.Binder x = binders.binder("x", POS);

        PathEngine.Entered in = engine.enteringArm(
                arm(new Core.ResolvedPattern.Single(CaseSelector.optionPresent(Type.INT)), x),
                answer, Known.top(), Denotations.none());

        FactSubject optional = engine.terms().subjectOf(answer, Denotations.none());
        FactSubject held = in.at().subject(x.id());
        assertNotNull(held, "what it binds is something to be known about");
        assertNotEquals(optional, held, "an optional is not what it holds");
        assertEquals(engine.terms().heldBy(optional), held);
    }

    /** Two arms opening one optional open one value, which is the same rule {@code Direct} obeys one
     * level up. Left alone, an optional would have kept the defect its own answer was given. */
    @Test
    void twoArmsOverOneOptionalOpenOneValue() {
        Core answer = optionalAnswer();
        Hir.Binder first = binders.binder("a", POS);
        Hir.Binder second = binders.binder("b", POS);

        FactSubject one = engine.enteringArm(
                arm(new Core.ResolvedPattern.Single(CaseSelector.optionPresent(Type.INT)), first),
                answer, Known.top(), Denotations.none()).at().subject(first.id());
        FactSubject other = engine.enteringArm(
                arm(new Core.ResolvedPattern.Single(CaseSelector.optionPresent(Type.INT)), second),
                answer, Known.top(), Denotations.none()).at().subject(second.id());

        assertEquals(one, other);
    }

    /** An optional written out holds what it was written with, so opening it names that value and
     * not a term standing over it. A constructor and what undoes it are one fact. */
    @Test
    void openingAWrittenOptionalNamesWhatItWasWrittenWith() {
        Core three = new Core.Int(3, Type.INT, POS);
        Core written = new Core.OptionSome(three, Type.option(Type.INT), POS);
        Hir.Binder x = binders.binder("x", POS);

        PathEngine.Entered in = engine.enteringArm(
                arm(new Core.ResolvedPattern.Single(CaseSelector.optionPresent(Type.INT)), x),
                written, Known.top(), Denotations.none());

        assertEquals(engine.terms().subjectOf(three, Denotations.none()),
                in.at().subject(x.id()));
    }

    /** The arm's name stands for the value it opened, and not for nothing. A reader following what a
     * name was given has to reach whatever produced it. */
    @Test
    void anArmsNameStandsForTheValueItOpened() {
        Core answer = answer();
        Hir.Binder x = binders.binder("x", POS);

        PathEngine.Entered in = engine.enteringArm(
                arm(new Core.ResolvedPattern.Single(CaseSelector.direct(FOUND)), x),
                answer, Known.top(), Denotations.none());

        assertEquals(answer, in.at().valueOf(x.id()),
                "what the arm opened is what its name was given");
    }

    /**
     * A {@code match} over what an outer arm bound finds the call underneath it.
     *
     * <p>The whole of why the name has to stand for the value and not only be about it: an arm
     * naming several cases says only that the answer is one of them, so what a rule states of one
     * case is taken in at the arm that names that case — which is a second {@code match}, over a
     * name, and the rule is found by following what that name was given.
     */
    @Test
    void aRuleAboutACaseReachesAMatchOverWhatAnOuterArmBound() {
        Core answer = numericAnswer();
        Hir.Binder x = binders.binder("x", POS);
        Hir.Binder y = binders.binder("y", POS);
        PathEngine reading = new PathEngine(Symbols.none(), Map.of(),
                Map.of(FIND, statesThatTheIntIsPositive()), Terms.Of.THE_DISCHARGE_TREE, souther.compiler.query.ReadAs.THE_COMPILATION_DOES);

        Denotations outer = reading.enteringArm(
                arm(new Core.ResolvedPattern.AnyOf(
                        List.of(CaseSelector.direct(AN_INT), CaseSelector.direct(MISSING)),
                        answer.type()), x),
                answer, Known.top(), Denotations.none()).at();
        Core.Case inner = arm(new Core.ResolvedPattern.Single(CaseSelector.direct(AN_INT)), y);
        PathEngine.Entered in = reading.enteringArm(inner,
                new Core.Read("x", x.id(), answer.type(), POS), Known.top(), outer);

        FactSubject opened = in.at().subject(y.id());
        assertTrue(in.known().speaksOf(opened),
                "the rule the behavior stated about its Int case was taken in here");
    }

    /** {@code ensures | Int v -> v > 0}, as the analysis holds it. */
    private static StatedContract statesThatTheIntIsPositive() {
        BindingId value = new Hir.Binders(new BindingOwner.OfValue("demo", "findIt"))
                .binder("v", POS).id();
        Core states = new Core.Binary(Hir.BinOp.GT,
                new Core.Read("v", value, Type.INT, POS), new Core.Int(0, Type.INT, POS),
                souther.compiler.types.CoverageOrigin.unwritten(), Type.BOOL, POS);
        return new StatedContract(FIND, List.of(), Type.INT,
                List.of(new StatedContract.StatedRule(new RuleId(FIND, 0, 0, AN_INT),
                        new Guard.Case(CaseSelector.direct(AN_INT)), value, Optional.empty(),
                        List.of(new StatedContract.Conjunct(POS,
                                new souther.compiler.check.TypedClause.Typed(states))))));
    }

    private Core.Case arm(Core.ResolvedPattern pattern, Hir.Binder binder) {
        return new Core.Case(pattern, binder, new Core.Read(binder.name(), binder.id(),
                pattern.bindType(), POS), POS);
    }

    private static Core answer() {
        return new Core.Call(ReachName.of(FIND, "findIt", "demo"), FIND, List.of(),
                Type.ref(FOUND), POS);
    }

    /** The same call, answering an optional — what an arm naming a present carrier is written over. */
    private static Core optionalAnswer() {
        return new Core.Call(ReachName.of(FIND, "findIt", "demo"), FIND, List.of(),
                Type.option(Type.INT), POS);
    }

    /** A call answering {@code Int | Missing}, which an arm may name either case of. */
    private static Core numericAnswer() {
        return new Core.Call(ReachName.of(FIND, "findIt", "demo"), FIND, List.of(),
                Type.union(new java.util.LinkedHashSet<>(List.of(AN_INT, MISSING))), POS);
    }
}
