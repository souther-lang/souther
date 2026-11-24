package souther.compiler.check;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.regex.WhatAStringSaysOfItsLength;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A relation a reading found stated of some values: this form, standing in this relation to nought.
 *
 * <p>What is said and not what it comes to. {@code x < 100} is this; that {@code x} lies between
 * nought and ninety-nine is what taking it into a domain answers, and that answer belongs to the
 * domain it was taken into. So this is the same value wherever it is read, which is what lets it be
 * recorded beside a recipe ({@link Derivation.Chosen}) where a range could not be.
 *
 * <p>Its own type and not one reader's. {@link Conditions} produces these, {@link Predicates} takes
 * them into what is known on a path, {@link Derivation.Chosen} records the ones choosing an arm
 * states, and {@link DerivedNumericFacts} both reads an arm under them and answers with them where
 * a recipe has a relation to state rather than a range. A vocabulary four readers share is not one
 * of their implementations — and it is one type and not two, since a relation a condition wrote and
 * a relation a reading derived go through the same door into a domain and differ in nothing a
 * reader of either could act on.
 */
record NumericConstraint(LinearForm<FactSubject> form, Rel rel)
        implements DerivedNumericFacts.Fact {

    /** The atoms this relation is written over. */
    Set<FactSubject> atoms() {
        return form.coefs().keySet();
    }

    /**
     * What each of {@code ways} makes certain, where the statement is one of them and which is not
     * said: of the same number, the weakest bound any of them puts on it.
     *
     * <p>Each way is a conjunction of relations. A bound on a number that every way states — each
     * as a lower bound, or each as an upper one — is stated by the one that allows the most, and a
     * number some way says nothing of is not bounded at all. Only lower and upper bounds are
     * compared: a relation between numbers that stands at no bound says nothing in common that
     * this could write down, and what is left out costs precision and never soundness.
     */
    static List<NumericConstraint> commonTo(List<List<NumericConstraint>> ways) {
        if (ways.isEmpty()) {
            return List.of();
        }
        List<Map<Map<FactSubject, ExactRatio>, ExactRatio>> lowest = new ArrayList<>();
        List<Map<Map<FactSubject, ExactRatio>, ExactRatio>> highest = new ArrayList<>();
        for (List<NumericConstraint> way : ways) {
            Map<Map<FactSubject, ExactRatio>, ExactRatio> lower = new LinkedHashMap<>();
            Map<Map<FactSubject, ExactRatio>, ExactRatio> upper = new LinkedHashMap<>();
            for (NumericConstraint each : way) {
                Map<FactSubject, ExactRatio> number = each.form().coefs();
                ExactRatio constant = each.form().constant();
                // `number + constant >= 0` is a lower bound of the number, and the strongest of
                // them is the one with the least constant; `<= 0` is an upper one, and the
                // strongest has the greatest.
                if (each.rel() == Rel.GE || each.rel() == Rel.EQ) {
                    lower.merge(number, constant, (one, other) -> one.compareTo(other) <= 0
                            ? one : other);
                }
                if (each.rel() == Rel.LE || each.rel() == Rel.EQ) {
                    upper.merge(number, constant, (one, other) -> one.compareTo(other) >= 0
                            ? one : other);
                }
            }
            lowest.add(lower);
            highest.add(upper);
        }
        List<NumericConstraint> out = new ArrayList<>();
        for (Map.Entry<Map<FactSubject, ExactRatio>, ExactRatio> first
                : lowest.getFirst().entrySet()) {
            ExactRatio weakest = first.getValue();
            boolean all = true;
            for (Map<Map<FactSubject, ExactRatio>, ExactRatio> way : lowest) {
                ExactRatio one = way.get(first.getKey());
                all &= one != null;
                weakest = one != null && one.compareTo(weakest) > 0 ? one : weakest;
            }
            if (all) {
                out.add(new NumericConstraint(new LinearForm<>(weakest, first.getKey()), Rel.GE));
            }
        }
        for (Map.Entry<Map<FactSubject, ExactRatio>, ExactRatio> first
                : highest.getFirst().entrySet()) {
            ExactRatio weakest = first.getValue();
            boolean all = true;
            for (Map<Map<FactSubject, ExactRatio>, ExactRatio> way : highest) {
                ExactRatio one = way.get(first.getKey());
                all &= one != null;
                weakest = one != null && one.compareTo(weakest) < 0 ? one : weakest;
            }
            if (all) {
                out.add(new NumericConstraint(new LinearForm<>(weakest, first.getKey()), Rel.LE));
            }
        }
        return out;
    }

    /** What {@code condition} of the lengths of strings, each named by an atom, states as a
     *  relation. */
    static NumericConstraint of(WhatAStringSaysOfItsLength.Condition<FactSubject> condition) {
        return switch (condition) {
            case WhatAStringSaysOfItsLength.Condition.AtLeast<FactSubject>(
                    FactSubject string, long length) -> new NumericConstraint(
                    LinearForm.atomMinusConstant(string, ExactRatio.of(length)), Rel.GE);
            case WhatAStringSaysOfItsLength.Condition.AtMost<FactSubject>(
                    FactSubject string, long length) -> new NumericConstraint(
                    LinearForm.atomMinusConstant(string, ExactRatio.of(length)), Rel.LE);
            case WhatAStringSaysOfItsLength.Condition.NoLongerThan<FactSubject>(
                    FactSubject inner, FactSubject outer) -> new NumericConstraint(
                    LinearForm.difference(inner, outer), Rel.LE);
            case WhatAStringSaysOfItsLength.Condition.Impossible<FactSubject> _ ->
                    new NumericConstraint(LinearForm.constant(ExactRatio.ONE.negated()), Rel.GE);
        };
    }
}
