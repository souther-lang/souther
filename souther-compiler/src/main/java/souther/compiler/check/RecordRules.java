package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * What each rule written on a record states, with the fields of the record the places it names are.
 *
 * <p>The one reading of a record's rules for the readers that ask what a rule says about two of its
 * fields together ({@link EntryHeld}, {@link SidesBalanced}). Read off what each rule states
 * ({@link InvariantStatements}), so a rule stated through a helper is the rule written out.
 *
 * <p>What is read of the rules is not what the record declares. A conjunct whose reading stopped
 * has no statements at all, so a record with a rule it could not read has fewer statements than
 * rules, and none where every rule stopped: {@link #statements} empty is no evidence that nothing
 * is declared. That is {@link #declared}, counted off what is written.
 *
 * @param fields     the name of each field, by the binding the rules name it by
 * @param statements every statement of every conjunct, the ones nothing was made of included
 * @param declared   how many conjuncts the record's rules are written as, whether or not any of
 *                   them was read
 */
record RecordRules(Map<BindingId, String> fields, List<InvariantStatement> statements,
                   int declared) {

    /** Whether the record declares no rule at all, which an unread rule is not. */
    boolean declaresNothing() {
        return declared == 0;
    }

    /**
     * The rules written on {@code named}, or null where it is not a record of its own fields: a
     * name wrapping a value has no field for a rule to relate to another.
     */
    static RecordRules of(TypeSymbol.AtModule named, RuleReadingSource source) {
        Map<BindingId, String> fields = new HashMap<>();
        source.bindings().of(named).forEach((name, binding) -> fields.put(binding, name));
        if (fields.isEmpty()
                || source.kinds().of(named.key()) != DeclarationKind.PRODUCT
                || source.newtypes().of(named.key())) {
            return null;
        }
        List<InvariantStatement> statements = new ArrayList<>();
        InvariantStatements read = InvariantStatements.ofTheCalls(source);
        int declared = 0;
        for (DeclaredClauses.OnAName written : DeclaredClauses.of(List.of(named), source)) {
            for (DeclaredClauses.Conjunct each : written.conjuncts()) {
                declared++;
                List<InvariantStatement> states = read.of(each.part());
                if (states != null) {
                    statements.addAll(states);
                }
            }
        }
        return new RecordRules(Map.copyOf(fields), List.copyOf(statements), declared);
    }

    /** The field the place {@code e} is, or null where it is no field of this record. */
    RuleKey fieldAt(Core e) {
        return ElementsApart.placeOf(e, fields, true);
    }
}
