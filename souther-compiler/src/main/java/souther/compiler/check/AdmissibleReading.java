package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.types.Type;
import souther.compiler.values.AdmissibleValues;
import souther.compiler.values.UnreadReason;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.math.BigDecimal;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The clauses reaching a value, read for which values each of its positions may hold.
 *
 * <p>Beside the reading that turns those same clauses into bounds, over the same list and at the
 * same moment. Which clauses reach a value is settled once, by the walk that gathers them, so the
 * two readings cannot come to disagree about what they were given; what each of them makes of a
 * clause is its own.
 *
 * <p>Apart from what a construction owes ({@link Predicates}), which is a different question and
 * has a different answer for the same clause. A clause stated as one of two alternatives owes a
 * construction nothing that a guard could discharge, and it says something here — so reading it
 * through the obligations would turn "some reading took this in" into "a construction may be held
 * to it", and a row would be offered at an edge promised by nothing.
 *
 * <p>Everything this cannot read is {@link AdmissibleValues#unreadable}, which widens and never
 * narrows. That is the whole discipline: a reading that answered "no value" from a clause it did
 * not read would refuse a model somebody can write. A denial is turned into what it leaves where
 * the values can be written out ({@link ValueUniverse}) and is kept as a denial where they cannot,
 * so nothing reaches emptiness except through values this had in hand.
 */
final class AdmissibleReading {

    private final Terms terms;
    private final Denotations at;
    /** What each position of the value is called, and what type stands there. A position is here
     * whether or not it is a number: which values a boolean has is as much an answer as which
     * values an integer has, and the reading that asked the carrier had no word for the first. */
    private final Map<Term, Type> byName;
    private final Symbols symbols;

    private AdmissibleReading(Terms terms, Denotations at, Map<Term, Type> byName,
                              Symbols symbols) {
        this.terms = terms;
        this.at = at;
        this.byName = byName;
        this.symbols = symbols;
    }

    /**
     * What {@code clauses} leave each position able to hold, all of them holding at once.
     *
     * @param byName the type at each position, keyed by what that position is called
     */
    static AdmissibleValues<Term> of(List<Core> clauses, Terms terms, Denotations at,
                                     Map<Term, Type> byName, Symbols symbols) {
        AdmissibleReading reading = new AdmissibleReading(terms, at, byName, symbols);
        AdmissibleValues<Term> out = AdmissibleValues.top();
        for (Core clause : clauses) {
            out = out.meet(reading.read(clause, true));
        }
        return out;
    }

    /**
     * What {@code e} says, stated where {@code positive} and denied where it is not.
     *
     * <p>A denial is carried to the leaves rather than applied to what a branch came to. What a
     * state says is a value per position, and the denial of that is not one — the values a
     * conjunction rules out are a choice between the positions it named, which no map of positions
     * holds. Carried down, every denial meets a comparison, where it is one.
     */
    private AdmissibleValues<Term> read(Core e, boolean positive) {
        Core under = Predicates.negated(e);
        if (under != null) {
            return read(under, !positive);
        }
        if (e instanceof Core.Binary b) {
            // Stated, a conjunction gives both sides; denied, it gives the choice between their
            // denials. And the same the other way round, which is the whole of what a denial does
            // to a connective.
            if (b.op() == Hir.BinOp.AND) {
                return positive ? read(b.left(), true).meet(read(b.right(), true))
                        : read(b.left(), false).join(read(b.right(), false));
            }
            if (b.op() == Hir.BinOp.OR) {
                return positive ? read(b.left(), true).join(read(b.right(), true))
                        : read(b.left(), false).meet(read(b.right(), false));
            }
            if (b.op() == Hir.BinOp.EQ || b.op() == Hir.BinOp.NE) {
                // Which of the two it states, once the denials above have been counted: `/=` denied
                // states the equality, and `==` denied denies it.
                return comparison(b, (b.op() == Hir.BinOp.EQ) == positive);
            }
        }
        return AdmissibleValues.unreadable(names(e), UnreadReason.FORM_NOT_READ);
    }

    /** What one comparison of a position with a value says, or nothing where it is not one. */
    private AdmissibleValues<Term> comparison(Core.Binary b, boolean states) {
        AdmissibleValues<Term> read = sided(b.left(), b.right(), states);
        if (read == null) {
            // `"A" == value` says what `value == "A"` says.
            read = sided(b.right(), b.left(), states);
        }
        return read != null ? read : AdmissibleValues.unreadable(names(b), whyNot(b));
    }

    /**
     * Why a comparison this reading recognised said nothing about the positions it names.
     *
     * <p>Told apart at the point of failure, where both sides are still in hand. A comparison of two
     * positions is a rule about a pair, and nothing about it was beyond this reading — a set of one
     * position's values is simply not what it says. A comparison against anything else is a form
     * this reading does not take apart, which is a fact about the reading. Recovered afterwards from
     * the positions alone, the two would be one answer.
     */
    private UnreadReason whyNot(Core.Binary b) {
        return positionIn(b.left()) != null && positionIn(b.right()) != null
                ? UnreadReason.RELATES_TWO_POSITIONS : UnreadReason.FORM_NOT_READ;
    }

    /** The same, with {@code where} read as the position and {@code what} as the value, or null
     * where they are not those. */
    private AdmissibleValues<Term> sided(Core where, Core what, boolean states) {
        Term position = positionIn(where);
        Type type = position == null ? null : byName.get(position);
        Value value = type == null ? null : valueOf(what);
        return value == null ? null : AdmissibleValues.at(position, admits(value, states, type));
    }

    /** The position {@code e} is, or null where it is not one of the positions being read for. */
    private Term positionIn(Core e) {
        Term named = terms.atomOf(e, at);
        if (named == null) {
            named = terms.bodyKey(e, at);
        }
        return named != null && byName.containsKey(named) ? named : null;
    }

    /**
     * The values a position of {@code type} is left by naming {@code value}, or by denying it.
     *
     * <p>A denial over a type whose values can be written out is the rest of them, which is how
     * {@code /= true} beside {@code /= false} comes to leave nothing. Over a type whose values
     * cannot be, it stays a denial and leaves no end of values, which is how {@code /= "A"} beside
     * {@code /= "B"} comes to leave almost everything.
     */
    private ValueSet admits(Value value, boolean states, Type type) {
        if (states) {
            return ValueSet.just(value);
        }
        List<Value> every = ValueUniverse.of(type, symbols);
        if (every == null) {
            return ValueSet.allBut(value);
        }
        Set<Value> left = new LinkedHashSet<>(every);
        left.remove(value);
        return ValueSet.oneOf(left);
    }

    /**
     * The value {@code e} is, or null where it is not one written out.
     *
     * <p>Read through the one fold there is, so a value written as an expression of values — two
     * strings joined — is the value it comes to. A case of an enumeration holds nothing and is not
     * folded to anything; what it is is which declaration it is.
     */
    private Value valueOf(Core e) {
        if (e instanceof Core.UnitValue unit) {
            return Value.of(unit.data());
        }
        Object folded = Terms.folded(e);
        if (folded instanceof String text) {
            return Value.text(text);
        }
        if (folded instanceof Boolean truth) {
            return Value.truth(truth);
        }
        if (folded instanceof Long whole) {
            return Value.number(whole);
        }
        return folded instanceof BigDecimal number ? Value.number(number) : null;
    }

    /**
     * The positions {@code e} names.
     *
     * <p>What a clause this could not read costs. It cannot cost a position it does not name:
     * nothing here relates one position to another, so a rule narrowing a position names it — and a
     * rule relating two of them names both and is itself one of these.
     */
    private Set<Term> names(Core e) {
        Set<Term> found = new LinkedHashSet<>();
        gather(e, found);
        return found;
    }

    private void gather(Core e, Set<Term> found) {
        Term here = terms.atomOf(e, at);
        if (here == null) {
            here = terms.bodyKey(e, at);
        }
        if (here != null && byName.containsKey(here)) {
            found.add(here);
            return;   // a position names itself, and nothing under it is a position of its own
        }
        Core.forEachChild(e, child -> gather(child, found));
    }
}
