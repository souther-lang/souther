package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructionOrigin;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * Applying a declared signature is one act, and a call settles it the same way wherever it is
 * applied: from what the context expects of the result, and then from what the value arguments state.
 *
 * <p>Held here because a difference between the two readers is not a failure anyone sees. A variable
 * settled from an empty collection instead of from the expected type leaves a closure typed over
 * {@code Nothing}, which either reports an arithmetic error in the author's own predicate or —
 * worse — types quietly and leaves an analysis reading a tree that says less than the one the backend
 * emits from.
 */
class OneCallSettlesOneSignatureTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final Preserved KEPT = Preserved.byTheLanguagesOwnOperations();
    private static final Ast.Binders BINDERS = new Ast.Binders(new BindingOwner.OfValue("demo", "t"));

    /** {@code List.filter(x -> true, [])} — nothing in the call says what the list holds. */
    private static Ast.Expr filterOverAnEmptyList() {
        Ast.Block predicate = new Ast.Block(List.of(BINDERS.binder("x", POS)),
                new Ast.BoolLit(true, POS), POS);
        return new Ast.Apply("List.filter", new ValueName.Stdlib("List", "filter"),
                List.of(predicate, new Ast.ListLit(List.of(), POS)), ConstructionOrigin.own(), POS);
    }

    @Test
    void anExpectedResultPinsAnEmptyContainerBeforeThePreservedClosureIsTyped() {
        Core typed = Elaborator.elaborate(filterOverAnEmptyList(), Scope.NONE,
                CheckContext.of(Symbols.none()).preserving(KEPT), Type.list(Type.INT));

        Core.PreservedCall kept = assertInstanceOf(Core.PreservedCall.class, typed);
        assertEquals(Type.list(Type.INT), kept.type(),
                "the position the call stands in is the only thing that says what the list holds");
    }

    @Test
    void andTheClosureIsTypedOverWhatWasPinnedRatherThanOverNothing() {
        Core typed = Elaborator.elaborate(filterOverAnEmptyList(), Scope.NONE,
                CheckContext.of(Symbols.none()).preserving(KEPT), Type.list(Type.INT));

        Core.PreservedCall kept = assertInstanceOf(Core.PreservedCall.class, typed);
        Core.Block predicate = assertInstanceOf(Core.Block.class, kept.args().get(0));
        assertEquals(List.of(Type.INT), ((Type.FnOf) predicate.type()).params(),
                "a predicate over `Nothing` is one the author's own body cannot use");
    }

    @Test
    void aFunctionHandedToAPreservedCallLearnsWhatTheValuesSettle() {
        // A lambda a `let` binds is never applied where a preserved call holds the application, so
        // what it takes is read off the declaration at the position it was handed to — through the
        // same settlement, so the parameter type that walk learns is the one the call reaches.
        String source = """
                module demo
                data Amount = Int
                    invariant value >= 1
                behavior f : (xs: List<Int>) -> List<Amount>
                    constructs Amount
                let f (xs) = {
                    let positive = y -> y > 0
                    List.map(y -> Amount(y), List.filter(positive, xs))
                }
                """;

        Compiler.Compiled compiled = Compiler.compileWithWarnings(source);

        assertFalse(compiled.classes().isEmpty(), "the function's parameter type was read");
    }

    @Test
    void everyValueArgumentIsReadOnceAndTheFunctionArgumentsNotAtAll() {
        // Reading an argument decides variables of the application it stands in, so a second reading
        // answers from the state the first one left. The settlement classifies and then unifies, and
        // both are that one reading.
        List<Type> params = List.of(
                Type.fn(List.of(new Type.Var("a", false)), Type.BOOL),
                Type.list(new Type.Var("a", false)));
        int[] reads = new int[params.size()];
        Ast.Apply call = (Ast.Apply) filterOverAnEmptyList();

        CallElaborator.settledByValues(call, params, Type.list(new Type.Var("a", false)),
                Type.list(Type.INT), i -> {
                    reads[i]++;
                    return Type.list(Type.INT);
                }, CheckContext.of(Symbols.none()));

        assertEquals(0, reads[0], "a function argument is typed after the values, not here");
        assertEquals(1, reads[1], "and a value argument is read once, however it is ordered");
    }

    @Test
    void anArgumentIsElaboratedOnceHoweverOftenARuleAsksItsType() {
        // The same guarantee where the answers come from: what a rule reasoned about and what reached
        // the tree are one elaboration of one argument.
        CallElaborator.CallArgs args = new CallElaborator.CallArgs(
                List.of(new Ast.IntLit(1, POS)), Scope.NONE, CheckContext.of(Symbols.none()));

        args.type(0);
        Core first = args.cores().get(0);
        args.type(0);

        assertSame(first, args.cores().get(0), "asked twice, elaborated once");
    }

    @Test
    void anArgumentThatAnswersNoValueDoesNotSettleWhatOneThatDoesHasSaid() {
        // Option.withDefault : ('a, Option<'a>) -> 'a. The empty list states nothing about what it
        // holds, so the option beside it is what decides — the other order holds the option to the
        // element type of nothing.
        Ast.Expr call = new Ast.Apply("Option.withDefault",
                new ValueName.Stdlib("Option", "withDefault"),
                List.of(new Ast.ListLit(List.of(), POS),
                        new Ast.Apply("List.get", new ValueName.Stdlib("List", "get"),
                                List.of(new Ast.IntLit(0, POS),
                                        new Ast.ListLit(List.of(new Ast.ListLit(
                                                List.of(new Ast.IntLit(1, POS)), POS)), POS)),
                                ConstructionOrigin.own(), POS)),
                ConstructionOrigin.own(), POS);

        Core typed = Elaborator.elaborate(call, Scope.NONE,
                CheckContext.of(Symbols.none()).preserving(KEPT));

        assertEquals(Type.list(Type.INT), typed.type());
    }
}
