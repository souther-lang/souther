package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.regex.PatternParser;
import souther.compiler.regex.PatternRead;
import souther.compiler.regex.PatternSyntax;
import souther.compiler.types.ValueName;
import souther.compiler.types.Type;
import souther.compiler.values.AdmittedPlan;
import souther.compiler.values.Allowance;
import souther.compiler.values.PlannedValues;
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
final class AdmissibleReading implements ClauseReading<PlannedValues<FactSubject>> {

    private final Terms terms;
    private final Denotations at;
    /** What each position of the value is called, and what type stands there. A position is here
     * whether or not it is a number: which values a boolean has is as much an answer as which
     * values an integer has, and the reading that asked the carrier had no word for the first. */
    private final Map<FactSubject, Type> byName;
    private final Symbols symbols;
    /** How a choice holds what it leaves, settled for the whole declaration before it was read. */
    private final Alternatives alternatives;
    /**
     * What puts two sets together, and what it is allowed to build doing it.
     *
     * <p>One of these for the whole of what is read into one answer, because that is what the
     * allowance is about: every rule reaching a position pays into the machine that position finally
     * admits. It is the reading's and not a leaf's, so a clause read here and a rule met with it
     * afterwards ({@code InvariantChecker}) spend from the same purse.
     */
    private final Allowance<FactSubject> allowed;

    private AdmissibleReading(Terms terms, Denotations at, Map<FactSubject, Type> byName,
                              Symbols symbols, Alternatives alternatives, Allowance<FactSubject> allowed) {
        this.terms = terms;
        this.at = at;
        this.byName = byName;
        this.symbols = symbols;
        this.alternatives = alternatives;
        this.allowed = allowed;
    }

    /** The reading of one value's positions, for {@link StatedByClauses} to take the leaves of. */
    static AdmissibleReading of(Terms terms, Denotations at, Map<FactSubject, Type> byName,
                                Symbols symbols, Alternatives alternatives, Allowance<FactSubject> allowed) {
        return new AdmissibleReading(terms, at, byName, symbols, alternatives, allowed);
    }

    /** What this reading is spending, for whoever meets its answer with the next rule's. */
    Allowance<FactSubject> allowed() {
        return allowed;
    }

    @Override
    public PlannedValues<FactSubject> nothingSaid() {
        return PlannedValues.top();
    }

    @Override
    public PlannedValues<FactSubject> both(PlannedValues<FactSubject> one, PlannedValues<FactSubject> other) {
        return one.meet(other);
    }

    /**
     * Either alternative holding, held apart or merged as the declaration was admitted.
     *
     * <p>Chosen before the reading and not while it folds. Merging only once some intermediate ran
     * past a limit would make what a position is answered turn on how the choice was bracketed, and
     * a model written two ways would be read two ways.
     */
    @Override
    public PlannedValues<FactSubject> either(PlannedValues<FactSubject> one, PlannedValues<FactSubject> other) {
        return alternatives == Alternatives.APART
                ? one.joinApart(other) : one.join(other);
    }

    /**
     * An equality names a value, a denial leaves the rest, and a pattern names the strings it
     * accepts; nothing else here is read.
     *
     * <p>A pattern is the third because a format is a third kind of answer and not because it is a
     * call. What {@code String.matches} says about a position is which strings stand there, which
     * is the question this reading asks — read as a call nobody follows, the rule said nothing and
     * a position an author had written a format for came out admitting every string there is.
     *
     * <p>And a position of two values is read as itself. Naming one is stating it, which is the
     * one value it then holds, and the polarity above says which — the reading of the clause has
     * already turned {@code p == false} and {@code p /= true} into this leaf denied
     * ({@link Conditions#restated}), so nothing here asks how the author spelled it.
     */
    @Override
    public PlannedValues<FactSubject> leaf(Core e, boolean positive) {
        if (e instanceof Core.Binary b
                && Comparison.of(b).map(Comparison::claim).orElse(null)
                        instanceof ComparisonClaim.Singled singled) {
            // Which of the two it states, once the denials above have been counted: what the
            // comparison holds at the value it names, turned over by each denial it stands under.
            return comparison(b, singled.holdsAtTheValue() == positive);
        }
        PlannedValues<FactSubject> truth = truthValued(e, positive);
        if (truth != null) {
            return truth;
        }
        PlannedValues<FactSubject> matched = pattern(e, positive);
        return matched != null ? matched : unreadable(e);
    }

    /** What naming a position of two values says about it, or null where {@code e} is not one. */
    private PlannedValues<FactSubject> truthValued(Core e, boolean states) {
        FactSubject position = positionIn(e);
        Type type = position == null ? null : byName.get(position);
        return type == Type.BOOL
                ? PlannedValues.at(position,
                        AdmittedPlan.of(admits(Value.truth(true), states, type)))
                : null;
    }

    /**
     * What a predicate over strings says about the position it is asked of, or null where the leaf
     * is not one.
     *
     * <p>Read whichever way it is stated. Denied, what stands is every string the predicate does
     * not accept, which is a set the same way — and reading only the stated form would leave a
     * denial as a form this cannot take apart, which of this very form would not be true.
     *
     * <p>Which calls these are, and what each says, is {@link StringPredicates}'. What is left here
     * is reaching the position and the written text and turning the answer into a plan — so a
     * predicate this reading learns is a row in that table and not an arm added here.
     *
     * <p>Null and not {@link AdmissibleValues#unreadable} for the leaves that are not this, so that
     * the one place a reading gives up stays where it is: what a rule this could not read costs is
     * worked out there, and a second answer to it here would be a second account of the same thing.
     */
    private PlannedValues<FactSubject> pattern(Core e, boolean states) {
        if (!(e instanceof Core.PreservedCall call)
                || !(call.operation() instanceof ValueName.Stdlib.Operation operation)) {
            return null;
        }
        StringPredicates predicate = StringPredicates.of(symbols.kernelOf(operation));
        if (predicate == null || call.args().size() != predicate.arity()) {
            return null;
        }
        FactSubject position = positionIn(call.args().get(predicate.subject()));
        if (position == null || !(Terms.folded(call.args().get(predicate.written()), symbols)
                instanceof String written)) {
            return null;
        }
        // What the author wrote, read through the fold above, so a format built out of pieces the
        // model names — a shared tail joined to a prefix — is the one string it comes to rather
        // than an expression nobody followed.
        PatternSyntax syntax;
        if (predicate.takesAPattern()) {
            PatternRead said = PatternParser.read(written);
            // Written more deeply than this reads is a limit of the reading and not a shape it has
            // no word for, so it is said as itself. Left to fall through, it would go out as a form
            // nothing here takes apart — and an author would go looking for the construct that was
            // the trouble, when every construct in it is one this reads.
            if (said instanceof PatternRead.NotRead it
                    && it.why() == souther.compiler.regex.PatternRead.Unsupported.NESTED_TOO_DEEPLY) {
                return PlannedValues.unreadable(Set.of(position),
                        UnreadReason.PATTERN_TOO_DEEPLY_NESTED);
            }
            if (!(said instanceof PatternRead.Read read)) {
                return null;
            }
            syntax = read.syntax();
        } else {
            // Text somebody looked for, which needs no reading: what it accepts is composed out of
            // the string itself, so there is no spelling of it this could fail to take apart.
            syntax = predicate.accepting(written);
        }
        // Named and not built. What the position finally admits is met out of every rule that
        // reached it, and a pattern met with three written strings is a question about three
        // strings — built here, it would be a machine nobody needed and the position would have
        // that much less for the meet it does need. So what is said is which machine would answer
        // this rule, and whether one is ever made of it is settled where the position's plan is
        // worked out under its allowance.
        return PlannedValues.at(position, new AdmittedPlan.Pattern(
                states ? souther.compiler.regex.PatternPlan.of(syntax)
                        : souther.compiler.regex.PatternPlan.notMatching(syntax)));
    }

    /** What one comparison of a position with a value says, or nothing where it is not one. */
    private PlannedValues<FactSubject> comparison(Core.Binary b, boolean states) {
        PlannedValues<FactSubject> read = sided(b.left(), b.right(), states);
        if (read == null) {
            // `"A" == value` says what `value == "A"` says.
            read = sided(b.right(), b.left(), states);
        }
        return read != null ? read : unreadable(b);
    }

    /**
     * A rule this reading could not turn into a set of values, and why.
     *
     * <p>How far this got and not how many positions the rule mentions. A comparison of one
     * position with another is a rule about a pair — {@code startsAt < endsAt}, {@code a /= b} —
     * and a set of one position's values is not what it says; nothing about it was beyond this
     * reading, which is what makes it its own answer rather than a shape nobody could read.
     * Anything else is a form this reading does not take apart, whatever it mentions.
     *
     * <p>Counting the positions instead reads {@code validPair(left, right)} as a relation, which
     * it may not be: what is known there is that two positions appear in an expression this could
     * not interpret, and the word it would be projected to says the rule relates them. The two
     * cases are told apart by what was recognised, at the one place a reading gives up, so an
     * ordering comparison and an equality answer alike — written per shape, {@code <} fell through
     * one path and {@code ==} another, and a relation came out as a form nobody could read.
     */
    private PlannedValues<FactSubject> unreadable(Core e) {
        return PlannedValues.unreadable(names(e), relatesTwoPositions(e)
                ? UnreadReason.RELATES_TWO_POSITIONS : UnreadReason.FORM_NOT_READ);
    }

    /**
     * Whether {@code e} is a comparison this reading recognised, of one position against another.
     *
     * <p>Which shapes those are is {@link Relates}'s and not this reading's, because the check that
     * classifies a clause for what it raises asks the same thing — and a shape counted here and not
     * there tells an author two different things about one clause. What stays here is how this
     * reading looks a position up.
     */
    private boolean relatesTwoPositions(Core e) {
        return Relates.twoPositions(e, this::positionIn);
    }

    /** The same, with {@code where} read as the position and {@code what} as the value, or null
     * where they are not those. */
    private PlannedValues<FactSubject> sided(Core where, Core what, boolean states) {
        FactSubject position = positionIn(where);
        Type type = position == null ? null : byName.get(position);
        Value value = type == null ? null : valueOf(what);
        return value == null ? null
                : PlannedValues.at(position, AdmittedPlan.of(admits(value, states, type)));
    }

    /** The position {@code e} is, or null where it is not one of the positions being read for. */
    private FactSubject positionIn(Core e) {
        FactSubject named = terms.subjectOf(e, at);
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
        Object folded = Terms.folded(e, symbols);
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
    private Set<FactSubject> names(Core e) {
        Set<FactSubject> found = new LinkedHashSet<>();
        gather(e, found);
        return found;
    }

    private void gather(Core e, Set<FactSubject> found) {
        FactSubject here = terms.subjectOf(e, at);
        if (here != null && byName.containsKey(here)) {
            found.add(here);
            return;   // a position names itself, and nothing under it is a position of its own
        }
        Core.forEachChild(e, child -> gather(child, found));
    }
}
