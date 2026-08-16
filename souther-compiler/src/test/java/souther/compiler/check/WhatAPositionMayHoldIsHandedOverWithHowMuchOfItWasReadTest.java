package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.query.Compilation;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which values a position is left, and whether that is the whole of what its rules leave it.
 *
 * <p>Two answers, and a reader needs both. A set of two values is a distinction the model draws at
 * that position, and the same set beside a rule this could not read is a distinction the model may
 * draw more finely. Told apart, a position nothing narrowed and a position this could not follow
 * are different reports; run together, the second is told the model divides it no way at all.
 *
 * <p>What refuses a declaration reads only the first, and reaching nothing is sound whatever the
 * second says: everything a set excludes is excluded by the rules, whether or not the rules say
 * more. So the answers below are held for the reader that divides a position rather than for the
 * one that refuses it.
 */
class WhatAPositionMayHoldIsHandedOverWithHowMuchOfItWasReadTest {

    /** One declaration read, and the module it was read in, so that a case of an enumeration can be
     * named the way the reading names it. */
    private record Read(FieldDomains domains, Symbols symbols) {

        Value caseNamed(String data) {
            return Value.of(TypeSymbols.declared(new TypeKey(symbols.module(), data)));
        }
    }

    private static Read read(String source, String named) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                .flatMap(List::stream)
                .map(each -> each.diagnostic().code())
                .toList(), "the model this reads has to be one somebody could write");
        Symbols symbols = compilation.symbols("demo");
        TypeSymbol name = TypeSymbols.declared(new TypeKey(symbols.module(), named));
        return new Read(FieldDomains.of(name,
                (Hir.Data) symbols.declarations().declaration(name.key()), symbols), symbols);
    }

    private static FieldDomains of(String source, String named) {
        return read(source, named).domains();
    }

    /** The same, for a model the compiler refuses: what this hands over afterwards is still read by
     * whatever ran before the refusal reached the caller. */
    private static FieldDomains ofRefused(String source, String named) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertFalse(compilation.diagnostics().values().stream().flatMap(List::stream).toList()
                .isEmpty(), "this model is meant to be refused");
        Symbols symbols = compilation.symbols("demo");
        TypeSymbol name = TypeSymbols.declared(new TypeKey(symbols.module(), named));
        return FieldDomains.of(name,
                (Hir.Data) symbols.declarations().declaration(name.key()), symbols);
    }

    private static final Value A = Value.text("A");
    private static final Value B = Value.text("B");

    /** {@code values} are what the position holds, and are the whole of what its rules leave it. */
    private static void wholly(ValueSet values, FieldDomains read, String path) {
        assertEquals(new FieldDomains.Admits.EveryRuleRead(values), read.admits(path));
    }

    /** {@code values} are what the position holds, and the rules may leave fewer. */
    private static void asFarAsRead(ValueSet values, FieldDomains read, String path) {
        assertEquals(new FieldDomains.Admits.SomeRuleUnread(values), read.admits(path));
    }

    /** An equality names the one value the position may hold. */
    @Test
    void anEqualityLeavesTheValueItNames() {
        FieldDomains read = of("""
                module demo

                data Gender = String
                    invariant only = value == "A"
                """, "Gender");
        wholly(ValueSet.just(A), read, FieldDomains.THE_VALUE);
    }

    /** Alternatives name both, which is the distinction a model writes this way. */
    @Test
    void alternativesLeaveEveryValueTheyName() {
        FieldDomains read = of("""
                module demo

                data Gender = String
                    invariant either = value == "A" || value == "B"
                """, "Gender");
        wholly(ValueSet.oneOf(Set.of(A, B)), read, FieldDomains.THE_VALUE);
    }

    /**
     * An alternative to a rule this cannot read leaves the position open, and says so.
     *
     * <p>Both halves matter and neither is the other. The values are open because a value
     * satisfying the second alternative is under no obligation from the first — and they are open
     * because of this reading, not because the model is silent about the position.
     */
    @Test
    void anAlternativeThatCannotBeReadLeavesThePositionOpenAndSaysWhy() {
        FieldDomains read = of("""
                module demo

                data Gender = String
                    invariant either = value == "A" || String.matches("[0-9]+", value)
                """, "Gender");
        asFarAsRead(ValueSet.ANY, read, FieldDomains.THE_VALUE);
    }

    /**
     * And where the alternative this cannot read never mentions the position at all.
     *
     * <p>The case the rule above is written for, and the one the case above does not reach: there
     * the unreadable alternative names {@code value}, so the position is spoiled by being named and
     * nothing about the alternative's being an alternative is asserted. Here nothing names
     * {@code left} but the branch that was read, and it is still a position this cannot speak for —
     * a value satisfying the other branch is under no obligation from this one, so what
     * {@code left} holds is open however plainly the first branch was read.
     */
    @Test
    void anAlternativeThatCannotBeReadSpoilsAPositionItNeverMentions() {
        FieldDomains read = of("""
                module demo

                data Pair = { left: String, right: String }
                    invariant either = left == "A" || String.matches("[0-9]+", right)
                """, "Pair");
        asFarAsRead(ValueSet.ANY, read, "left");
    }

    /**
     * A rule this cannot read stated beside one it can takes nothing away from what the read one
     * says, and leaves the position one this cannot speak for.
     *
     * <p>Both halves again, and the second is not the first being cautious. What is left is every
     * value the rules admit and may be more: the same shape with {@code "[0-9]"} in it admits
     * nothing at all, and this reading answers {@code "A"} to both. Sound for refusing — nothing is
     * excluded that the rules allow — and not a division of the position, which is what saying so
     * is for.
     */
    @Test
    void aRuleThatCannotBeReadBesideOneThatCanCostsTheValuesNothingAndTheDivisionEverything() {
        FieldDomains read = of("""
                module demo

                data Gender = String
                    invariant both = value == "A" && String.matches("[A-Z]", value)
                """, "Gender");
        asFarAsRead(ValueSet.just(A), read, FieldDomains.THE_VALUE);
    }

    /** And a rule it cannot read that names another position costs this one nothing at all.
     *
     * <p>Nothing here relates one position to another, so a rule that narrows a position names it —
     * which is what makes the answer above local rather than a whole declaration's worth of
     * caution. */
    @Test
    void aRuleThatCannotBeReadAboutAnotherPositionCostsThisOneNothing() {
        FieldDomains read = of("""
                module demo

                data Pair = { left: String, right: String }
                    invariant both = left == "A" && String.matches("[A-Z]", right)
                """, "Pair");
        wholly(ValueSet.just(A), read, "left");
        asFarAsRead(ValueSet.ANY, read, "right");
    }

    /** A rule this cannot read on its own leaves the position open, and says that it did. */
    @Test
    void aRuleThatCannotBeReadAtAllLeavesThePositionOpenAndSaysWhy() {
        FieldDomains read = of("""
                module demo

                data Gender = String
                    invariant shape = String.matches("[A-Z]", value)
                """, "Gender");
        asFarAsRead(ValueSet.ANY, read, FieldDomains.THE_VALUE);
    }

    /** A position with no rules at all is open, and this can say so: the model divides it in no
     * way, which is a different answer from the one above and reads the same here. */
    @Test
    void aPositionWithNoRulesIsOpenAndSpokenFor() {
        FieldDomains read = of("""
                module demo

                data Gender = String
                """, "Gender");
        wholly(ValueSet.ANY, read, FieldDomains.THE_VALUE);
    }

    /** A denial over an enumeration leaves the cases it did not deny. */
    @Test
    void aDenialOverAnEnumerationLeavesTheCasesItDidNotDeny() {
        Read read = read("""
                module demo

                data Red
                data Green
                data Blue
                data Colour = Red | Green | Blue

                data Painted = { colour: Colour }
                    invariant notRed = colour /= Red
                """, "Painted");
        wholly(ValueSet.oneOf(Set.of(read.caseNamed("Green"), read.caseNamed("Blue"))),
                read.domains(), "colour");
        // And in the order the model declares them. What is written out of these is a class per
        // value, and a reader listing them takes the order it is given — so the order has to be one
        // the model settled rather than one a set happened to store them in, which for an immutable
        // copy is settled afresh on every run of the compiler.
        assertEquals(List.of(read.caseNamed("Green"), read.caseNamed("Blue")),
                List.copyOf(((ValueSet.Finite) read.domains().admits("colour").values()).values()));
    }

    /**
     * A reading that never ran says of every position that a rule about it may be unread.
     *
     * <p>Which is the answer that costs something to get wrong. A reading that fell over, and one a
     * caller never asked for, leave the same empty maps a value with no rules leaves — and the
     * empty answer read as "the model divides this position in no way at all" is the widest claim
     * there is, made where nothing was read.
     */
    @Test
    void aReadingOfNothingSpeaksForNoPosition() {
        asFarAsRead(ValueSet.ANY, FieldDomains.NONE, FieldDomains.THE_VALUE);
        asFarAsRead(ValueSet.ANY, FieldDomains.NONE, "anything");
    }

    /**
     * And a clause nothing could type leaves every position of its declaration the same way.
     *
     * <p>Such a clause reaches no reading at all, so no reading here knows which position it was
     * about — and a position it might have divided is one this cannot claim to have read. The
     * declaration is refused where the clause is written; what is asserted here is that a reader
     * asking this one afterwards is not told something untrue.
     */
    @Test
    void aClauseNothingCouldTypeLeavesNoPositionSpokenFor() {
        FieldDomains read = ofRefused("""
                module demo

                data Pair = { left: String, right: Int }
                    invariant no = left == "A" && right == "B"
                """, "Pair");
        asFarAsRead(ValueSet.ANY, read, "left");
        asFarAsRead(ValueSet.ANY, read, "right");
    }

    /** And the rules of one field say nothing about another. */
    @Test
    void whatOneFieldMayHoldIsNotWhatTheFieldBesideItMayHold() {
        FieldDomains read = of("""
                module demo

                data Pair = { left: String, right: String }
                    invariant one = left == "A"
                """, "Pair");
        wholly(ValueSet.just(A), read, "left");
        wholly(ValueSet.ANY, read, "right");
    }
}
