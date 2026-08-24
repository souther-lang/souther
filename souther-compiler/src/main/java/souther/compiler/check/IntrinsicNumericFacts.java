package souther.compiler.check;

import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.ConstantArguments;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.ResultBound;
import souther.compiler.semantics.SizeAgainstItsSource;
import souther.compiler.core.Core;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;

/**
 * What a value carries by being the value it is, read off the operation that answered it.
 *
 * <p>The third source of what an arm or a step may be read under, beside what a condition states
 * ({@link Conditions}) and what a declaration guarantees of a value built through its checked
 * constructor ({@link TypeGuarantees}). Neither of those covers it. A condition did not say a length
 * is at or above nought — {@code not List.isEmpty(xs)} says it is not nought, and the rest is the
 * list's — and no declaration says it either: {@code List} writes no clause about its length, and
 * what a library operation guarantees of its answer is a contract rather than a data invariant. So
 * it is a source of its own, and until #988 it had no owner and no place to be recorded.
 *
 * <p><b>One node, and no traversal.</b> What is answered here is what <em>this</em> call's answer
 * carries, and the walk to whatever else the expression names is not here. Held the other way — as
 * {@code sizeFacts} and {@code resultFacts} were, recursing through {@link Core#forEachChild} —
 * reading these facts meant having the tree, which meant only a reader that had one could have them:
 * a reduction's step is forms and atoms by the time it is read, and everything it named came out
 * unbounded whatever it was (#988). The recursion is not needed either, because {@link Terms} is
 * already walking the expression to name it, and an atom that files what it carries where it is
 * named leaves nothing for a second walk to collect.
 *
 * <p>Relations and one edge each. Where a size is no greater than the size of what it was built
 * from, what is stated here is that one relation and not the chain behind it: naming the source's
 * size files what <em>it</em> carries, and the chain comes back as reachability
 * ({@link Terms#reached}) rather than as a walk this makes. So a rule added to the table states one
 * thing, wherever in a chain it lands.
 *
 * <p>Functions and no state, as {@link Conditions} is. {@link Terms} is passed because a relation is
 * written over atoms and only that reader names one; nothing here decides what an atom is called.
 *
 * <p>Nothing here is a rule of its own. Which operations guarantee what is {@link DischargeRules}'
 * tables — {@code SIZES}, {@code BOUNDS_ON_THE_RESULT}, {@code LOWER_BOUNDS}, {@code BUILDINGS} —
 * and this is the one reader of them that turns a row into a relation between atoms.
 */
final class IntrinsicNumericFacts {

    /**
     * A call whose arguments none of its operation's rows name, which is what a measure is: it is
     * given a container, and a bound may only name an argument that is a number
     * ({@link DischargeRules#holdBound}). So the rows read under this are all of them, and the one
     * premise is written here rather than once for the condition on the arguments and again for the
     * argument a row stands against.
     */
    private static final java.util.function.Function<ArgumentRef, LinearForm<FactSubject>>
            NO_ARGUMENTS = _ -> null;

    private IntrinsicNumericFacts() {}

    /**
     * What the size {@code atom} carries: it is never negative, and it stands where the sizes of the
     * containers this one was built from put it.
     *
     * <p>{@code container} is the container the atom is the size of, which is the one a construction
     * keeping its source's size has already been peeled off of ({@link DischargeRules#sizeSource}) —
     * the same peeling the atom's own name was made through, so that what is stated here is stated
     * about the atom it is filed against and not about a neighbour of it.
     */
    static List<NumericConstraint> ofSize(ValueName size, Core container, FactSubject atom,
                                          Denotations at, Terms terms) {
        List<NumericConstraint> out = new ArrayList<>();
        // What the measure itself states of what it answers, which is that a count is at or above
        // nought. Read off the operation's rows and not written here: it is the same proposition as
        // `Int.abs(x) >= 0`, and a copy of it here was the half of it a partition could not reach
        // (#1016).
        bounding(DischargeRules.boundsOn(size, ConstantArguments.NONE), atom, NO_ARGUMENTS, out);
        // A construction's result is no smaller than each source the rule names for it. A rule may
        // name more than one — `a ++ b` is as long as either half — so this is a loop where the
        // building below is one answer.
        for (Core added : DischargeRules.noSmallerThan(container)) {
            standing(size, atom, added, Rel.GE, at, terms, out);
        }
        if (container instanceof Core.PreservedCall call) {
            DischargeRules.Source built = DischargeRules.builtFrom(call);
            Rel rel = built == null ? null : relationOf(built.size());
            if (rel != null) {
                standing(size, atom, built.container(), rel, at, terms, out);
            }
        }
        return out;
    }

    /** States how {@code atom} stands to the size of {@code source}, where that size is one this can
     * name. A container nothing names is one nothing is stated about, which leaves the size bounded
     * by what else is known of it rather than by half a rule. */
    private static void standing(ValueName size, FactSubject atom, Core source, Rel rel,
                                 Denotations at, Terms terms, List<NumericConstraint> out) {
        FactSubject there = terms.sizeAtomFor(size, source, at);
        if (there != null && !there.equals(atom)) {
            out.add(new NumericConstraint(LinearForm.atom(atom).minus(LinearForm.atom(there)), rel));
        }
    }

    /** How a size is stated of the two, or null where there is nothing to state: a construction of
     * the same size answers both with one atom ({@link DischargeRules#sizeSource}), so a relation
     * between them would say a name stands to itself. */
    private static Rel relationOf(SizeAgainstItsSource size) {
        return switch (size) {
            case AT_MOST -> Rel.LE;
            case SAME -> null;
        };
    }

    /**
     * What the answer of {@code call} carries whatever its arguments are: an absolute value is not
     * negative, a remainder by a written divisor is below it.
     *
     * <p>A bound whose rule asks something of the arguments is stated only where the arguments
     * answer, and what they are read as is the naming's answer — a name given a constant is that
     * constant, here as everywhere.
     */
    static List<NumericConstraint> ofCall(Core.PreservedCall call, FactSubject atom, Denotations at,
                                          Terms terms) {
        List<NumericConstraint> out = new ArrayList<>();
        bounding(DischargeRules.boundsOn(call, arg -> constantOf(arg, at, terms)), atom,
                ref -> terms.affineOf(CallArguments.of(ref, call), at), out);
        shifted(call, atom, at, terms, out);
        return out;
    }

    /**
     * The rows as what they say about {@code atom}, keeping the relation to the argument each names.
     *
     * <p>The one reader of a {@link ResultBound} that keeps it whole. A range of one number cannot
     * hold {@code floorMod(x, k) < k}, so the projection onto one ({@link
     * souther.compiler.semantics.ResultRange}) drops it; here the argument has a name, and what the
     * row says is what is stated.
     *
     * <p>{@code against} answers the argument a row names. A row it cannot answer states nothing,
     * which is what a bound against a quantity this reader has no name for comes to.
     */
    private static void bounding(List<ResultBound> rows, FactSubject atom,
                                 java.util.function.Function<ArgumentRef,
                                         LinearForm<FactSubject>> against,
                                 List<NumericConstraint> out) {
        for (ResultBound bound : rows) {
            LinearForm<FactSubject> stands = bound.against() == null
                    ? LinearForm.constant(bound.offset())
                    : addTo(against.apply(bound.against()), bound.offset());
            if (stands != null) {
                out.add(new NumericConstraint(LinearForm.atom(atom).minus(stands), bound.rel()));
            }
        }
    }

    /**
     * What a measure between two values comes to where the second of them is the first moved by an
     * amount: exactly that amount, in the units the shift states it in.
     *
     * <p>Asked of the measure and not of the shift, which is where it is about the atom it is filed
     * against. A shift's own answer is a date and no number, so a rule filed where the shift is
     * written would be filed against a value the numeric reading has no name for — and the measure is
     * the value the fact is about, the one a clause writing that measure names and the one this is
     * read back through.
     *
     * <p>Read through the names either side was given: {@code let then = Date.addDays(d, n)} and the
     * shift written out are one value, and a measure to either is the same measure.
     */
    private static void shifted(Core.PreservedCall call, FactSubject atom, Denotations at,
                                Terms terms, List<NumericConstraint> out) {
        if (!DischargeRules.isAMeasure(call.operation()) || call.args().size() != 2) {
            return;
        }
        if (!(terms.originating(call.args().get(1), at, new java.util.HashSet<>())
                instanceof Core.PreservedCall moved)) {
            return;
        }
        OperationFact.ShiftsBy shift = DischargeRules.shiftBy(moved);
        if (shift == null || !shift.measure().equals(call.operation())
                || !sameValue(CallArguments.of(shift.of(), moved), call.args().get(0), at, terms)) {
            return;
        }
        LinearForm<FactSubject> amount = terms.affineOf(CallArguments.of(shift.amount(), moved), at);
        if (amount != null) {
            out.add(new NumericConstraint(
                    LinearForm.atom(atom).minus(amount.times(shift.per())), Rel.EQ));
        }
    }

    /** Whether the two expressions are one value, which is whether the term grammar names them
     * alike. */
    private static boolean sameValue(Core a, Core b, Denotations at, Terms terms) {
        Term one = terms.bodyKey(a, at);
        return one != null && one.equals(terms.bodyKey(b, at));
    }

    /** {@code form} with {@code offset} added, or null where the form could not be read. */
    private static LinearForm<FactSubject> addTo(LinearForm<FactSubject> form, BigDecimal offset) {
        return form == null ? null : form.plus(LinearForm.constant(offset));
    }

    /** The constant {@code e} reads as, or null where it reads as none. */
    private static BigDecimal constantOf(Core e, Denotations at, Terms terms) {
        LinearForm<FactSubject> form = terms.affineOf(e, at);
        return form == null || !form.coefs().isEmpty() ? null : form.constant();
    }
}
