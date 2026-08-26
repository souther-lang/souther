package souther.compiler.partition;

import souther.compiler.check.DeclaredBorders;
import souther.compiler.check.RuleRef;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Optional;

/**
 * One line of the model: which rule, and which of that rule's lines.
 *
 * <p>What the author wrote, with nothing about the reading that reached it. A rule is read once per
 * position of every behavior carrying it and once per call of every helper holding it, and none of
 * that is here — no position, no behavior, no occurrence, no place a body arrived at it by. Those
 * are {@link OriginRef}'s, which is which reading of the rule this is, and this is what several
 * readings of one line share.
 *
 * <p><b>Not the rule alone.</b> One clause places as many lines as it has conjuncts with an end in
 * them: {@code invariant within = value >= 1 && value <= 10} is one {@link RuleRef.Invariant} and
 * two lines, and a row at the bottom of the range is no evidence about the top. So which conjunct
 * drew it is part of this, and it is the clause's own text rather than the number it was written
 * about ({@link souther.compiler.check.DeclaredBounds.Drawn}).
 *
 * <p><b>And what the line is.</b> Two lines of one rule at one value are told apart by what each
 * says about its own value ({@link LineFacts}) — {@code value >= 5 && value <= 5} places a minimum
 * and a maximum at 5, and they are two lines however few values are left between them. Whether some
 * row could show the two apart is not asked: what row is left over is a fact about every other rule
 * of the model, so an identity read off it would be worked back out of what the rules happened to
 * leave rather than read from what this rule says.
 *
 * @param rule           which rule of the model drew it
 * @param conjunct       which of that rule's lines this is, counted over the conjuncts the author
 *                       wrote. Zero for a rule that draws one line, which is what a comparison and
 *                       an {@code ensures} clause each do
 * @param facts          what the rule says about its own line
 * @param narrowedWithin the declarations that took a bound's end in, kept so that a narrowed line
 *                       stays apart from the bare one it narrows: {@code MinuteOfDay}'s maximum is
 *                       the same rule whether or not {@code WorkInterval} moved where it lands, and
 *                       the line the two settled together is not the line the bound would have
 *                       drawn alone
 */
public record AuthoredLine(RuleRef rule, int conjunct, LineFacts facts,
                           List<TypeSymbol> narrowedWithin) {

    public AuthoredLine {
        if (rule == null || facts == null) {
            throw new IllegalArgumentException("a line of the model is some rule's, and says what it"
                    + " is: " + rule + " " + facts);
        }
        if (conjunct < 0) {
            throw new IllegalArgumentException(
                    "a conjunct of a rule is counted from zero: " + conjunct);
        }
        narrowedWithin = List.copyOf(narrowedWithin);
    }

    /**
     * What a report calls this line.
     *
     * <p>The rule's own name, and the declarations that took it in beside it. A narrowing is not
     * part of the rule, so the rule does not say it and this does.
     *
     * <p>A name and not a place, because a debt is not at one: a line an {@code invariant} drew is
     * met wherever the type is carried, so any place to print would be the position of whichever
     * behavior a walk reached first. Where a reading of it is being named rather than the line, the
     * place is said by {@link OriginRef#describe}.
     */
    public String named() {
        return said(rule.named());
    }

    /**
     * The same about a rule a reader is calling something else.
     *
     * <p>A comparison has no name, so a reading of one is said by where it is written
     * ({@link OriginRef#describe}) — and what the narrowing adds is the same words either way. Said
     * in both places, the two spellings of one narrowing read as two.
     */
    public String said(String rule) {
        return rule + (narrowedWithin.isEmpty() ? ""
                : " within " + narrowedWithin.stream().map(TypeSymbol::name)
                        .collect(java.util.stream.Collectors.joining(" or ")));
    }

    /**
     * The declaration this line is owed to, where it is a declaration's line rather than a body's.
     *
     * <p>Whose debt a row at the line is. A clause of a {@code data} says something about the type
     * wherever the type is carried, so a row standing at the line is evidence about the type and the
     * behaviors carrying it have nothing to add — one line, owed once, at the declaration that wrote
     * it. A comparison and an {@code ensures} clause are written in a body and say something about
     * that body at that position, so they are owed per behavior.
     *
     * <p>A narrowed end is the bound's declaration. The declarations that took it in are what
     * {@link #named} says beside the rule, and each of them is one where taking any away leaves the
     * end where it is — so there is no one of them to send a reader to, and the rule that placed the
     * end is where the line came from.
     */
    public Optional<TypeSymbol> owedToTheDeclaration() {
        return rule instanceof RuleRef.Invariant i
                ? Optional.of(i.clause().id().declaredOn())
                : Optional.empty();
    }

    /**
     * Which authored line of a declaration this is, where it is a declaration's line.
     *
     * <p>The clause and the conjunct that drew the end, which together name one line the author
     * wrote — what a report reads the declaration's own words for the line by
     * ({@link DeclaredBorders}).
     */
    public Optional<DeclaredBorders.Key> declaredLine() {
        return rule instanceof RuleRef.Invariant i
                ? Optional.of(new DeclaredBorders.Key(i, conjunct))
                : Optional.empty();
    }
}
