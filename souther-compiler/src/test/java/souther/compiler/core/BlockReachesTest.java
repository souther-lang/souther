package souther.compiler.core;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ReachName;
import souther.compiler.types.ResolvedCase;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What {@link BlockReaches} answers about a {@link Core.Block}: the lexical boundary a {@code let},
 * a {@code match} arm's binder and a nested block each draw, and the partition between a behavior
 * call this block's construction requires injected and every other named reach.
 */
class BlockReachesTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "b");
    private static final ValueName.Behavior ORDINARY = new ValueName.Behavior("demo", "ordinary");
    private static final ValueName.Behavior INJECTED = new ValueName.Behavior("demo", "injected");
    private static final TypeSymbol.AtModule CASE = TypeSymbols.declared(new TypeKey("demo", "Thing"));

    @Test
    void aLetsBinderDoesNotShieldItsOwnValue() {
        BindingId bound = binding(0);
        // let b = b in b — the right-hand `b` names no binding yet, so it is a reach; the left-hand
        // `b` in the body is the let's own and is not.
        Core.LetIn let = new Core.LetIn(new Core.Binder("b", bound), Type.INT, read(bound), read(bound),
                Type.INT, POS);
        Core.Block block = block(let);

        BlockReaches reaches = BlockReaches.of(block, Set.of());

        assertEquals(List.of(bound), bindingIds(reaches),
                "the value is read before its own let binds anything, so its read of the same"
                        + " binding is a reach; the body's read of what the let just bound is not");
    }

    @Test
    void aMatchArmsBinderDoesNotReachIntoASiblingArm() {
        BindingId first = binding(0);
        BindingId second = binding(1);
        Core.Case sees = new Core.Case(pattern(), new Core.Binder("x", first), read(first), POS);
        // this arm's body reads the other arm's binder, which its own scope never bound
        Core.Case leaks = new Core.Case(pattern(), new Core.Binder("y", second), read(first), POS);
        Core.Match match = new Core.Match(read(second), List.of(sees, leaks),
                Core.ForkPlace.asWritten(ConstructOccurrence.unwritten()), Type.INT, POS);
        Core.Block block = block(match);

        BlockReaches reaches = BlockReaches.of(block, Set.of());

        assertEquals(List.of(second, first), bindingIds(reaches),
                "the scrutinee's binding and the read a sibling arm's body makes of the other arm's"
                        + " binder are both reaches; a binder's own arm reading it is not");
    }

    @Test
    void anIfConstructedsBinderScopesOnlyItsSuccessArm() {
        BindingId x = binding(0);
        // if constructed x = ... then read(x) else read(x) — the binder scopes `then` alone, so
        // the same binding read from a failure arm never entered its scope.
        Core.IfConstructed attempted = new Core.IfConstructed(construction(),
                new Core.Binder("x", x), read(x),
                List.of(new Core.ElseArm(Optional.empty(), read(x))),
                Core.ForkPlace.asWritten(ConstructOccurrence.unwritten()), Type.INT, POS);
        Core.Block block = block(attempted);

        BlockReaches reaches = BlockReaches.of(block, Set.of());

        assertEquals(List.of(x), bindingIds(reaches),
                "the binder scopes only the success arm: its own read there is not a reach, but the"
                        + " same binding read from a failure arm is, since the binder never scoped"
                        + " it");
    }

    @Test
    void aNestedBlocksOuterReachIsTheOuterBlocksReachToo() {
        BindingId outerParam = binding(0);
        BindingId outside = binding(1);
        Core.Block inner = block(binary(read(outerParam), read(outside)));
        Core.Block outer = new Core.Block(List.of(new Core.Binder("x", outerParam)), inner,
                Type.INT, POS);

        BlockReaches outerReaches = BlockReaches.of(outer, Set.of());
        BlockReaches innerReaches = BlockReaches.of(inner, Set.of());

        assertEquals(List.of(outside), bindingIds(outerReaches),
                "the outer block binds its own parameter, so only the read of what is outside both"
                        + " blocks reaches past the outer block's own boundary");
        assertEquals(List.of(outerParam, outside), bindingIds(innerReaches),
                "the inner block binds neither name, so both the outer block's parameter and what is"
                        + " outside both reach past the inner block's own boundary");
    }

    @Test
    void aBindingReadTwiceIsCountedOnceAtItsFirstOccurrence() {
        BindingId x = binding(0);
        Core.Block block = block(binary(read(x), read(x)));

        BlockReaches reaches = BlockReaches.of(block, Set.of());

        assertEquals(List.of(x), bindingIds(reaches),
                "a binding read more than once is one reach, at the position it was first read");
    }

    @Test
    void aRequirementAndAnOrdinaryDeclarationPartitionEvenWhenBothAreCalled() {
        Core call = binary(callOf(ORDINARY), callOf(INJECTED));
        Core.Block block = block(call);

        BlockReaches reaches = BlockReaches.of(block, Set.of(INJECTED));

        assertEquals(List.of(ORDINARY), declarationNames(reaches),
                "a call this block's construction does not require injected is a declaration reach");
        assertEquals(List.of(INJECTED), reaches.requirements(),
                "a call to a behavior this block's construction requires injected is a requirement,"
                        + " not a declaration");
    }

    @Test
    void anEmittedOperationIsNoNamedReach() {
        Core call = new Core.Call(Core.Emitted.BUILD_LIST, List.of(), ConstructOccurrence.unwritten(),
                Core.CallSettlement.None.INSTANCE, Type.INT, POS);
        Core.Block block = block(call);

        BlockReaches reaches = BlockReaches.of(block, Set.of());

        assertEquals(List.of(), reaches.declarations(),
                "an operation this compiler emits names no declaration, so it is not a named reach");
        assertEquals(List.of(), reaches.requirements());
    }

    private static List<BindingId> bindingIds(BlockReaches reaches) {
        return reaches.bindings().stream().map(Core.Read::binding).toList();
    }

    private static List<ValueName.Behavior> declarationNames(BlockReaches reaches) {
        return reaches.declarations().stream()
                .map(reached -> (ValueName.Behavior) reached.denotes()).toList();
    }

    private static BindingId binding(int index) {
        return new BindingId(OWNER, index);
    }

    private static Core.Read read(BindingId binding) {
        return new Core.Read("x", binding, Type.INT, POS);
    }

    private static Core.Block block(Core body) {
        return new Core.Block(List.of(), body, Type.INT, POS);
    }

    private static Core binary(Core left, Core right) {
        return new Core.Binary(BinOp.ADD, left, right, ConstructOccurrence.unwritten(), Type.INT,
                POS);
    }

    private static Core callOf(ValueName.Behavior behavior) {
        return new Core.Call(new Core.Reached.OfDeclaration(new ReachName.Own(behavior)),
                List.of(), ConstructOccurrence.unwritten(), Core.CallSettlement.None.INSTANCE,
                Type.INT, POS);
    }

    private static Core.ResolvedPattern pattern() {
        return new Core.ResolvedPattern.Single(ResolvedCase.of(CaseSelector.direct(CASE),
                List.of(CASE)));
    }

    private static Core.Construct construction() {
        return new Core.Construct(CASE, List.of(), Type.ref(CASE), POS);
    }
}
