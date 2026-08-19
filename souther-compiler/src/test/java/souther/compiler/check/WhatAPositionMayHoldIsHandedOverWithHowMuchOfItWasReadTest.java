package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Scopes;
import souther.compiler.ast.Hir;
import souther.compiler.query.Compilation;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.AdmissibleSet;
import souther.compiler.values.UnreadReason;
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
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
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
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        TypeSymbol name = TypeSymbols.declared(new TypeKey(symbols.module(), named));
        return FieldDomains.of(name,
                (Hir.Data) symbols.declarations().declaration(name.key()), symbols);
    }

    private static final Value A = Value.text("A");
    private static final Value B = Value.text("B");

    /** {@code values} are what the position holds, and are the whole of what its rules leave it. */
    private static void wholly(ValueSet values, FieldDomains read, String path) {
        assertEquals(AdmissibleSet.complete(values), read.admits(path));
    }

    /** {@code values} are what the position holds, the rules may leave fewer, and {@code why} is
     *  what stopped the reading short of them. */
    private static void asFarAsRead(ValueSet values, UnreadReason why, FieldDomains read,
                                    String path) {
        assertEquals(AdmissibleSet.partial(values, why), read.admits(path));
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
        asFarAsRead(ValueSet.ANY, UnreadReason.FORM_NOT_READ, read, FieldDomains.THE_VALUE);
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
        asFarAsRead(ValueSet.ANY, UnreadReason.ALTERNATIVE_NOT_READ, read, "left");
    }

    /**
     * And what such a position is told is that an alternative took it back, whatever the unread
     * branch was about.
     *
     * <p>{@code left /= right} relates two positions and {@code code} is neither of them, so the
     * reason the branch stopped is not a reason about {@code code}. Lent across, a report would
     * tell an author that a rule compares {@code code} with another position, and no rule does.
     *
     * <p>The two positions that rule does name are left whole. {@code code == "A"} says nothing
     * about either of them, so a {@code Triple} with any {@code left} at all satisfies the choice
     * by its second alternative — and what a position may hold is every value, which is the whole
     * of what the rules leave it. That the relating rule went unread is a fact about the rules and
     * is answered by the accounting, not by what a position may hold.
     */
    @Test
    void aPositionAnAlternativeTookBackIsNotToldWhatTheOtherBranchWasAbout() {
        FieldDomains read = of("""
                module demo

                data Triple = { left: String, right: String, code: String }
                    invariant either = left /= right || code == "A"
                """, "Triple");

        asFarAsRead(ValueSet.ANY, UnreadReason.ALTERNATIVE_NOT_READ, read, "code");
        wholly(ValueSet.ANY, read, "left");
        wholly(ValueSet.ANY, read, "right");
    }

    /**
     * What covered a position is an alternative, and a rule beside the choice may leave none of it.
     *
     * <p>{@code a == 5} admits every {@code b}, so the choice does and nothing about {@code b} went
     * unread — while that alternative stands. {@code a == 7} refuses every value it admits, and what
     * is left is {@code a /= b} with {@code a} at 7, which is a rule this cannot read about a
     * {@code b} that is now not every value. A reading that had struck the rule off where the
     * choice was read would answer that the model leaves {@code b} every value and that this was
     * read in full.
     */
    @Test
    void whatCoveredAPositionCanBeRefusedByARuleBesideTheChoice() {
        FieldDomains read = of("""
                module demo

                data R = { a: Int, b: Int }
                    invariant one = a == 5 || a /= b
                    invariant two = a == 7
                """, "R");

        asFarAsRead(ValueSet.just(Value.number(7)), UnreadReason.RELATES_TWO_POSITIONS, read, "a");
        asFarAsRead(ValueSet.ANY, UnreadReason.RELATES_TWO_POSITIONS, read, "b");
    }

    /**
     * A choice over two positions leaves nothing for an alternative beside it to rest on.
     *
     * <p>Read one position at a time, each of the two choices leaves {@code a} open, and so does
     * what they leave together — but the pairs they agree on are only {@code a = 5, b = 0}, since
     * an {@code a} of anything else is asked for with {@code b = 1} by one and with {@code b = 0}
     * by the other. What the rules leave {@code a} is {@code 5} and whatever the third alternative
     * admits, and no reading here can say the third alternative admits anything.
     *
     * <p>So the position is one this cannot speak for. A reading that read what each position holds
     * on its own and offered that as cover would answer that the model divides {@code a} no way at
     * all, on the strength of a pair no value of this type takes.
     */
    @Test
    void aChoiceOverTwoPositionsCoversNothingForTheAlternativeBesideIt() {
        FieldDomains read = of("""
                module demo

                data R = { a: Int, b: Int }
                    invariant said =
                        (((a == 5 && b == 0) || (a /= 5 && b == 1))
                         && ((a == 5 && b == 0) || (a /= 5 && b == 0)))
                        || Int.abs(a) >= 2
                """, "R");

        asFarAsRead(ValueSet.ANY, UnreadReason.FORM_NOT_READ, read, "a");
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
        asFarAsRead(ValueSet.just(A), UnreadReason.FORM_NOT_READ, read, FieldDomains.THE_VALUE);
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
        asFarAsRead(ValueSet.ANY, UnreadReason.FORM_NOT_READ, read, "right");
    }

    /**
     * A rule relating two positions is told apart from one written in a form this cannot read.
     *
     * <p>Both leave the positions open and neither is the other. Nothing about {@code left /= right}
     * was beyond this reading — both sides were recognised, and what it says is a fact about the
     * pair, which a set of one position's values is not. A regex over one of them is a form this
     * reading does not take apart, which is a fact about the reading and is lifted by different
     * work.
     *
     * <p>Told apart where the reading gave up, since that is the only place both sides are still in
     * hand. Recovered afterwards from the spoiled positions alone, the two would be one answer.
     */
    @Test
    void aRuleRelatingTwoPositionsIsNotARuleWrittenInAFormThisCannotRead() {
        FieldDomains related = of("""
                module demo

                data Pair = { left: String, right: String }
                    invariant differ = left /= right
                """, "Pair");
        asFarAsRead(ValueSet.ANY, UnreadReason.RELATES_TWO_POSITIONS, related, "left");
        asFarAsRead(ValueSet.ANY, UnreadReason.RELATES_TWO_POSITIONS, related, "right");

        FieldDomains shaped = of("""
                module demo

                data Pair = { left: String, right: String }
                    invariant shape = String.matches("[A-Z]", left)
                """, "Pair");
        asFarAsRead(ValueSet.ANY, UnreadReason.FORM_NOT_READ, shaped, "left");
    }

    /**
     * A position compared with itself is related to nothing, and is not said to be.
     *
     * <p>Two operands and one position. The reading recognises the comparison and finds a position
     * on each side, which is not the same as finding two — and the word it would be projected to
     * says the rule relates this position to another, when the model wrote no other. What is true
     * of it is that this reading did not take the rule in.
     */
    @Test
    void aPositionComparedWithItselfIsRelatedToNothing() {
        asFarAsRead(ValueSet.ANY, UnreadReason.FORM_NOT_READ, of("""
                module demo

                data Code = String
                    invariant same = value == value
                """, "Code"), FieldDomains.THE_VALUE);

        FieldDomains fields = of("""
                module demo

                data Pair = { left: String, right: String }
                    invariant same = left /= left
                """, "Pair");
        asFarAsRead(ValueSet.ANY, UnreadReason.FORM_NOT_READ, fields, "left");
    }

    /**
     * And a call over two positions is a form this could not read, not a relation between them.
     *
     * <p>What is known of {@code validPair(left, right)} is that two positions appear in something
     * this reading could not interpret. Whether the rule says anything about how they stand against
     * each other is exactly what was not worked out, so counting the positions and calling it a
     * relation says more than the reading found — and the word it is projected to tells the author
     * their rule compares one position with another.
     */
    @Test
    void aCallOverTwoPositionsIsAFormNotARelation() {
        FieldDomains read = of("""
                module demo

                let validPair (a: String, b: String) = String.length(a) == String.length(b)

                data Pair = { left: String, right: String }
                    invariant paired = validPair(left, right)
                """, "Pair");

        asFarAsRead(ValueSet.ANY, UnreadReason.FORM_NOT_READ, read, "left");
        asFarAsRead(ValueSet.ANY, UnreadReason.FORM_NOT_READ, read, "right");
    }

    /** A rule this cannot read on its own leaves the position open, and says that it did. */
    @Test
    void aRuleThatCannotBeReadAtAllLeavesThePositionOpenAndSaysWhy() {
        FieldDomains read = of("""
                module demo

                data Gender = String
                    invariant shape = String.matches("[A-Z]", value)
                """, "Gender");
        asFarAsRead(ValueSet.ANY, UnreadReason.FORM_NOT_READ, read, FieldDomains.THE_VALUE);
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
                List.copyOf(((ValueSet.Finite) read.domains().admits("colour").approximation())
                        .values()));
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
        asFarAsRead(ValueSet.ANY, UnreadReason.NOT_REACHED, FieldDomains.NONE,
                FieldDomains.THE_VALUE);
        asFarAsRead(ValueSet.ANY, UnreadReason.NOT_REACHED, FieldDomains.NONE, "anything");
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
        asFarAsRead(ValueSet.ANY, UnreadReason.NOT_REACHED, read, "left");
        asFarAsRead(ValueSet.ANY, UnreadReason.NOT_REACHED, read, "right");
    }

    /**
     * And a clause nothing could type inside a field's own type leaves that field the same way.
     *
     * <p>A rule reaches a position from wherever it is written — the record the position is a field
     * of, and the declarations under that record it sits inside — so a clause lost anywhere on that
     * descent is a clause no reading here saw. Which position it was about is exactly what is not
     * known, so the field it was lost under is one this cannot speak for.
     */
    @Test
    void aClauseNothingCouldTypeInsideAFieldsTypeLeavesThatFieldSpokenForByNothing() {
        FieldDomains read = ofRefused("""
                module demo

                data Inner = String
                    invariant no = value == 1

                data Outer = { inner: Inner }
                """, "Outer");
        asFarAsRead(ValueSet.ANY, UnreadReason.NOT_REACHED, read, "inner");
    }

    /**
     * A type the walk does not enter leaves its rules unread, and that is said too.
     *
     * <p>The walk goes through a field's own type and stops at what wraps one — an optional, a
     * collection, a sum of records — so a rule written inside one of those reaches no reading here.
     * A position whose values those rules narrow is not one this can speak for, however plainly the
     * clauses it did read were read.
     */
    @Test
    void aRuleUnderSomethingTheWalkDoesNotEnterIsARuleUnread() {
        asFarAsRead(ValueSet.ANY, UnreadReason.NOT_REACHED, of("""
                module demo

                data Inner = String
                    invariant only = value == "A"

                data Outer = { inner: Inner? }
                """, "Outer"), "inner");
        asFarAsRead(ValueSet.ANY, UnreadReason.NOT_REACHED, of("""
                module demo

                data Inner = String
                    invariant only = value == "A"

                data Outer = { inners: List<Inner> }
                """, "Outer"), "inners");
        asFarAsRead(ValueSet.ANY, UnreadReason.NOT_REACHED, of("""
                module demo

                data Yes = { n: Int }
                    invariant only = n == 1
                data No = { n: Int }
                data Answer = Yes | No

                data Outer = { answer: Answer }
                """, "Outer"), "answer");
    }

    /**
     * A stop under one field says nothing about the field beside it.
     *
     * <p>Where the walk stopped and not that it stopped. A rule that narrows a position names it,
     * and a clause written inside one field can name no position outside that field — so a walk
     * that declined to go into a list of constrained values has said nothing about the plain
     * {@code Int} next to it, and the {@code Int} is a position nothing was written about.
     *
     * <p>Recorded as one answer for the whole value, this was the common shape in the corpus: a
     * record with one field the walk stops at leaves every other field of it reported as one whose
     * rules may have gone unread, when nothing was written about them at all.
     */
    @Test
    void aStopUnderOneFieldDoesNotSpoilTheFieldBesideIt() {
        FieldDomains read = of("""
                module demo

                data Inner = String
                    invariant only = value == "A"

                data Forecast = { inners: List<Inner>, dealCount: Int }
                """, "Forecast");

        asFarAsRead(ValueSet.ANY, UnreadReason.NOT_REACHED, read, "inners");
        wholly(ValueSet.ANY, read, "dealCount");
    }

    /** And a clause of the value's own declaration reaches every position of it, so a stop there
     *  leaves all of them short of their rules. */
    @Test
    void aStopAtTheValueItselfLeavesEveryPositionOfItShort() {
        FieldDomains read = ofRefused("""
                module demo

                data Pair = { left: String, right: Int }
                    invariant no = left == "A" && right == "B"
                """, "Pair");

        asFarAsRead(ValueSet.ANY, UnreadReason.NOT_REACHED, read, "left");
        asFarAsRead(ValueSet.ANY, UnreadReason.NOT_REACHED, read, "right");
    }

    /**
     * And a type it does not enter that no rule is written under costs nothing.
     *
     * <p>Which is what keeps the answer worth having. A record with a plain field, or with a field
     * of an enumeration, is a record the walk stops at twice and loses nothing at either stop — a
     * unit data may write no rule (spec §unit-data), and a primitive has none to write. A reading
     * that said so at every stop would speak for no position of any record that has a field.
     */
    @Test
    void aTypeTheWalkDoesNotEnterCostsNothingWhereNoRuleIsWrittenUnderIt() {
        wholly(ValueSet.ANY, of("""
                module demo

                data Outer = { plain: String }
                """, "Outer"), "plain");
        wholly(ValueSet.ANY, of("""
                module demo

                data Red
                data Green
                data Colour = Red | Green

                data Outer = { colour: Colour }
                """, "Outer"), "colour");
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
