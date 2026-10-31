package souther.compiler.partition;

import souther.compiler.check.Choice;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ElementsWrittenOut;
import souther.compiler.check.Symbols;
import souther.compiler.check.ValueStanding;
import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.inputs.WrittenOutElements;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;

/**
 * What the reading of a body's names comes to, in the shape the walks over a body ask for.
 *
 * <p>Two walks meet every name of a body — the arithmetic that finds the line a rule draws, and the
 * one that says which positions a rule is about — and each asks its own interface for the same two
 * facts. What a name means is {@link InputReads#meaningOf}'s single answer; what is here is the
 * projection of that answer onto the pair those interfaces are written in.
 *
 * <p>Written once because the two walks disagreeing about a name is not a difference of opinion but
 * a defect with a shape: one of them reads a rule and draws its line while the other cannot name the
 * position the line divides, after which the position is reported as one the model divides no way.
 * Kept as two copies, that is one edit away at all times.
 */
final class NameAnswers {

    /** The one value {@code read}'s name denotes, or null where it denotes none. */
    static ValueStanding.ReadThrough<InputReads> denoting(Core.Read read, InputReads at,
                                                        Symbols symbols,
                                                        DeclarationNewtypes newtypes) {
        return at.meaningOf(read, symbols, newtypes) instanceof ReadMeaning.Through through
                ? asked(through.denotes()) : null;
    }

    /**
     * Every value {@code read}'s name can stand for, or null where the reading has not got them all.
     *
     * <p>A container this reading cannot write out answers nothing here. One it can is answered with
     * the value of every occurrence there on some row, as {@code kept} decides: what a reader keeps
     * is what every member comes to, and a value no run has is no member — counted, one this reading
     * could not follow would leave the ones that are there unread. Where none is there on any row,
     * no value is handed and nothing is answered.
     */
    static List<ValueStanding.ReadThrough<InputReads>> alternativesOf(Core.Read read, InputReads at,
                                                                    Symbols symbols,
                                                                    DeclarationNewtypes newtypes,
                                                                    ReadMeaning.WhereKept kept) {
        if (!(at.meaningOf(read, symbols, newtypes) instanceof ReadMeaning.OneOf one)) {
            return null;
        }
        List<ValueStanding.ReadThrough<InputReads>> each = new ArrayList<>();
        one.valuesWhere(kept).forEach(stands -> each.add(asked(stands)));
        return each.isEmpty() ? null : each;
    }

    /** What the reading {@code at} takes {@code node} as, or null where it takes it as nothing
     *  else ({@link InputReads#taken}). */
    static ValueStanding.ReadThrough<InputReads> taken(Core node, InputReads at) {
        Denotation as = at.taken(node);
        return as == null ? null : asked(as);
    }

    /**
     * The arm of the match {@code node} that a run takes, where it matches on a lookup that finds an
     * element of a list written out ({@link ElementsWrittenOut#picked}) and working the lookup out,
     * and what each name in it was given, ends no run: the arm taking {@code Some}, read where
     * choosing it puts the reading. Null where the lookup settles nothing, which leaves the match
     * to be read some other way.
     *
     * <p>Which arm is taken is a question of values; what is worked out to reach the lookup is
     * asked of the scrutinee as it is written. The arms the lookup rules out are not read, so what
     * they would end a run for is not asked.
     */
    static ValueStanding.ReadThrough<InputReads> armOfAMatchOnAFoundElement(
            Core node, InputReads at, Symbols symbols, DeclarationNewtypes newtypes,
            WorkedOutToReachIt reached) {
        if (!(Core.withoutStanding(node) instanceof Core.Match match)
                || !reached.endsNoRun(new Denotation(match.scrutinee(), at))
                || ElementsWrittenOut.picked(match.scrutinee(), at,
                        WrittenOutElements.reading(symbols, newtypes)) == null) {
            return null;
        }
        for (Core.Case arm : match.cases()) {
            if (arm.pattern() != null && arm.pattern().takes(TypeSymbol.SOME)) {
                return new ValueStanding.ReadThrough<>(arm.body(), at.choosing(
                        new Choice.Decides.ACase(arm, match.scrutinee()), symbols, newtypes));
            }
        }
        return null;
    }

    /** The form of the values it was given the reading {@code at} takes the call {@code node} as,
     *  or null where it takes it as none ({@link InputReads#takenAsAForm}). */
    static LinearForm<Core> takenAsAForm(Core node, InputReads at) {
        return at.takenAsAForm(node);
    }

    /** A value and what to read it in, as the walks spell that pair. */
    private static ValueStanding.ReadThrough<InputReads> asked(Denotation stands) {
        return new ValueStanding.ReadThrough<>(stands.value(), stands.at());
    }

    private NameAnswers() {}
}
