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
 * <p>What is read of the rules is not what the record declares, and what is not found in them is not
 * known to be absent. A conjunct whose reading stopped has no statements at all, and a declaration
 * whose rules could not be expanded lists none of them: either way {@link #statements} is short of
 * the rules with nothing in it to say so. The counts and the completeness beside it are what say
 * it, and a reader asking whether a record has a rule of some kind, or has none, asks them
 * ({@link #declaresNothing}, {@link #readInFull}) and never the emptiness of what was found.
 *
 * @param fields           the name of each field, by the binding the rules name it by
 * @param statements       every statement of every conjunct, the ones nothing was made of included
 * @param declared         how many conjuncts the record's rules are written as, whether or not any
 *                         of them was read
 * @param unread           how many of those nothing was made of: a rule that left no statement,
 *                         and a statement that is only a statement that something was written
 * @param everyRuleReached whether every declaration whose rules govern the record was expanded
 */
record RecordRules(Map<BindingId, String> fields, List<InvariantStatement> statements,
                   int declared, int unread, boolean everyRuleReached) {

    /** Whether the record is shown to declare no rule at all: none is written and none was left
     *  out. An unread rule is a rule, and so is one that could not be reached. */
    boolean declaresNothing() {
        return declared == 0 && everyRuleReached;
    }

    /** Whether every rule of the record was reached and something was made of each, so that what
     *  is not among the statements is not in the rules. */
    boolean readInFull() {
        return unread == 0 && everyRuleReached;
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
        int unread = 0;
        boolean everyRuleReached = true;
        for (DeclaredClauses.OnAName written : DeclaredClauses.of(List.of(named), source)) {
            everyRuleReached &= written.everyRuleReached();
            for (DeclaredClauses.Conjunct each : written.conjuncts()) {
                declared++;
                List<InvariantStatement> states = read.of(each.part());
                if (states == null) {
                    unread++;
                } else {
                    statements.addAll(states);
                    // The denial of a rule of a kind something is built for: it asks the opposite
                    // of what the rules beside it are built to, and was read as nothing. The
                    // statements this reading has no form for besides are most comparisons, which
                    // ask nothing of what is built and are not counted.
                    unread += (int) states.stream()
                            .filter(one -> one instanceof InvariantStatement.Unread it
                                    && it.denies())
                            .count();
                }
            }
        }
        return new RecordRules(Map.copyOf(fields), List.copyOf(statements), declared, unread,
                everyRuleReached);
    }

    /** The field the place {@code e} is, or null where it is no field of this record. */
    RuleKey fieldAt(Core e) {
        return ElementsApart.placeOf(e, fields, true);
    }
}
