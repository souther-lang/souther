package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a declaration guarantees, asked of the reading itself.
 *
 * <p>{@link TypeGuarantees} answers one question for every reader there is: a walk seeding a path,
 * and a recipe settling a choice. Each of those has tests of its own about what it does with the
 * answer, and those are the tests that pass while the answer is wrong — a walk can agree with itself
 * about a declaration it reads two levels too shallowly. So the answer is held here, on its own.
 *
 * <p>What is fixed is what a position guarantees and where the positions are. How far a reader goes
 * is not fixed and may not be: two readers walking to different depths are still reading one model,
 * and requiring one depth would put a reader's affordance inside what a declaration means. What is
 * required instead is the last test here — where two scopes both looked, they were told the same
 * thing.
 */
class WhatATypeGuaranteesIsOneAnswerWhoeverAsksTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static final String SOURCE = """
            module demo exposing ( Money, Wrapped, Chain, Plain, keep )

            data NonNegInt = Int
                invariant value >= 0

            data Money = { amount: NonNegInt }

            data Wrapped = Money

            data Chain = { here: NonNegInt, next: List<Chain> }

            data Plain = { label: String }

            behavior keep : (m: Money) -> Money

            let keep (m) = m
            """;

    private final Symbols symbols = symbols();

    private final PathEngine engine = new PathEngine(symbols, Map.of(),
            Terms.Of.THE_DISCHARGE_TREE, souther.compiler.query.ReadAs.THE_COMPILATION_DOES);

    private final GuaranteeWalk walk = new GuaranteeWalk(engine.guarantees());

    private static Symbols symbols() {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        compilation.answerEverything();
        return Scopes.derived(compilation.db(), compilation.modules().get(0)).value();
    }

    private static TypeSymbol named(String name) {
        return TypeSymbols.declared(new TypeKey("demo", name));
    }

    /** A place of type {@code name}, and the reading that has it named. */
    private Read place(String name) {
        BindingId binding = CoreBinders
                .of(new Hir.Binders(new BindingOwner.OfValue("demo", "keep")).binder("v", POS))
                .binding();
        Core.Read root = new Core.Read("v", binding, Type.ref(named(name)), POS);
        Denotations at = Denotations.none().location(binding, engine.terms().placeSubject(binding),
                engine.terms().placeTerm(binding));
        return new Read(root, at);
    }

    private record Read(Core.Read root, Denotations at) {}

    /** Every clause the walk was told about, by the position it was told at. */
    private Map<String, List<String>> guaranteedUnder(String name, GuaranteeWalk.Scope scope) {
        Map<String, List<String>> out = new LinkedHashMap<>();
        Read read = place(name);
        walk.from(read.root(), FieldDomains.THE_VALUE, read.at(), scope,
                (path, guarantee) -> out.computeIfAbsent(path, _ -> new ArrayList<>())
                        .add(guarantee.rule().clause().toString()));
        return out;
    }

    /** Every position the walk stopped at, and why. */
    private Map<String, GuaranteeWalk.Stop> stoppedIn(String name, GuaranteeWalk.Scope scope) {
        Map<String, GuaranteeWalk.Stop> out = new LinkedHashMap<>();
        Read read = place(name);
        walk.from(read.root(), FieldDomains.THE_VALUE, read.at(), scope,
                new GuaranteeWalk.Reader() {
                    @Override
                    public void guaranteed(String path, TypeGuarantee guarantee) {}

                    @Override
                    public void stopped(String path, Type type, GuaranteeWalk.Stop why) {
                        out.put(path, why);
                    }
                });
        return out;
    }

    /**
     * A clause written on a field's type is a rule about that field of this value, at that field's
     * position.
     */
    @Test
    void aFieldIsAPositionOfItsOwn() {
        assertEquals(List.of("amount"),
                List.copyOf(guaranteedUnder("Money", GuaranteeWalk.Scope.asFarAs(2)).keySet()),
                "Money writes no clause of its own; NonNegInt's is about the amount");
    }

    /**
     * A newtype's value is the same location as the newtype, so what its base guarantees is
     * guaranteed of this very atom. Wearing a name is not being somewhere else.
     */
    @Test
    void aNewtypeCarriesWhatItsBaseGuaranteesAtItsOwnPosition() {
        assertEquals(List.of("amount"),
                List.copyOf(guaranteedUnder("Wrapped", GuaranteeWalk.Scope.asFarAs(2)).keySet()),
                "Wrapped is Money, which is at no path of its own, so its field is the first step");
    }

    /** A declaration writing nothing, and nothing written under it, guarantees nothing. */
    @Test
    void aDeclarationWithNoRuleUnderItGuaranteesNothing() {
        assertTrue(guaranteedUnder("Plain", GuaranteeWalk.Scope.asFarAs(2)).isEmpty(),
                "a record of a String writes no rule and holds nothing that does");
    }

    /**
     * A record holding another of its own kind stops rather than descending for ever, and stopping
     * there is not being short of anything: the name was read where it was met.
     */
    @Test
    void aRecordHoldingItsOwnKindIsReadWhereItWasMet() {
        Map<String, List<String>> guaranteed =
                guaranteedUnder("Chain", GuaranteeWalk.Scope.asFarAs(6));

        assertEquals(List.of("here"), List.copyOf(guaranteed.keySet()),
                "the chain's own field is read once, and the list under it reaches no further");
        assertFalse(stoppedIn("Chain", GuaranteeWalk.Scope.asFarAs(6)).isEmpty(),
                "and the walk says where it stopped rather than going round again");
    }

    /**
     * A depth a reader could not afford is a stop and not an answer.
     *
     * <p>Which is why the depth may not live in the reading: a position left unread is one this
     * reader did not reach, and saying nothing about it would be saying no rule stands there.
     */
    @Test
    void aDepthTheReaderCouldNotAffordIsAStop() {
        assertTrue(guaranteedUnder("Money", GuaranteeWalk.Scope.asFarAs(0)).isEmpty(),
                "the amount is one position down, and this reader asked for none");
        assertEquals(GuaranteeWalk.Stop.PAST_THE_DEPTH,
                stoppedIn("Money", GuaranteeWalk.Scope.asFarAs(0)).get("amount"),
                "and it is told that it stopped there rather than that nothing was written");
    }

    /** A name a reader supposes holds values is not descended into, and nothing under it is read. */
    @Test
    void aNameTheReaderStopsAtIsNotDescendedInto() {
        GuaranteeWalk.Scope stopping =
                new GuaranteeWalk.Scope(4, named("NonNegInt")::equals, _ -> false);

        assertTrue(guaranteedUnder("Money", stopping).isEmpty(),
                "the only clause under Money is NonNegInt's, and this reader stops there");
        assertEquals(GuaranteeWalk.Stop.ASKED_TO_STOP, stoppedIn("Money", stopping).get("amount"));
    }

    /** A declaration's own clauses may be left out while what is under it is still read. */
    @Test
    void aDeclarationsOwnClausesCanBeLeftOutWithoutLeavingWhatIsUnderIt() {
        GuaranteeWalk.Scope without =
                new GuaranteeWalk.Scope(4, _ -> false, named("NonNegInt")::equals);

        assertTrue(guaranteedUnder("Money", without).isEmpty(),
                "NonNegInt's clause is the one left out");
        assertEquals(GuaranteeWalk.Stop.NOTHING_DECLARED, stoppedIn("Money", without).get("amount"),
                "and the position was still entered and walked through — the stop under it is the"
                        + " whole number a newtype wraps, which declares nothing, and not this"
                        + " reader being told to go no further");
    }

    /**
     * One reading and many readers.
     *
     * <p>The contract itself: two scopes are two walks, and where both of them looked they were told
     * the same thing. A reader that could afford less is short of positions, never of a different
     * answer about one.
     */
    @Test
    void twoScopesAreToldTheSameThingWhereBothLooked() {
        Map<String, List<String>> shallow =
                guaranteedUnder("Chain", GuaranteeWalk.Scope.asFarAs(1));
        Map<String, List<String>> deep = guaranteedUnder("Chain", GuaranteeWalk.Scope.asFarAs(6));

        assertFalse(shallow.isEmpty(), "a reading saying nothing would agree with anything");
        shallow.forEach((path, clauses) -> assertEquals(clauses, deep.get(path),
                "what stands at " + path + " is what stands there, however far the reader went"));
    }
}
