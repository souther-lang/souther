package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
 * @param unread           how many of those left no statement at all, which is a rule whose reading
 *                         stopped and whose places are not known
 * @param everyRuleReached whether every declaration whose rules govern the record was expanded
 * @param readByOthers     the fields a rule reads from that no consumer builds for, other than to
 *                         count what they hold
 */
record RecordRules(Map<BindingId, String> fields, List<InvariantStatement> statements,
                   int declared, int unread, boolean everyRuleReached,
                   Set<String> readByOthers) {

    /**
     * Whether a rule that nothing here builds for reads from the field {@code field}, other than to
     * count what it holds.
     *
     * <p>The question a builder asks before it takes a field on: it builds the field holding what
     * the rules it knows ask of it, and is right only if no other rule asks anything else of the
     * field. A rule is told apart by where it reads from and not by what it says, so a denial, a
     * denied choice and a rule written through a helper are all the same to it. How many a field
     * holds is the count the range of its values already carries, so a rule reading the field only
     * through that is no other rule.
     */
    boolean readFromByOthers(String field) {
        return readByOthers.contains(field);
    }

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
                }
            }
        }
        // Where the rules nothing is built for read from, whatever they say.
        Set<String> readByOthers = new HashSet<>();
        for (InvariantStatement one : statements) {
            switch (one) {
                case InvariantStatement.Unread it -> readFrom(it.said(), fields, readByOthers);
                case InvariantStatement.Compares it -> {
                    readFrom(it.states().left(), fields, readByOthers);
                    readFrom(it.states().right(), fields, readByOthers);
                }
                case InvariantStatement.Applies it -> {
                    if (EntryHeld.read(it.call(), core -> core) == null) {
                        readFrom(it.call(), fields, readByOthers);
                    }
                }
                case InvariantStatement.HoldsAnEntry _, InvariantStatement.BalancesSides _ -> { }
            }
        }
        return new RecordRules(Map.copyOf(fields), List.copyOf(statements), declared, unread,
                everyRuleReached, Set.copyOf(readByOthers));
    }

    /** The fields of the record {@code e} reads, other than as the thing a count is taken of. */
    private static void readFrom(Core e, Map<BindingId, String> fields, Set<String> out) {
        Core node = Core.withoutStanding(e);
        if (node instanceof Core.PreservedCall call
                && NumericMeasures.isMeasure(call.operation())) {
            return;
        }
        if (node instanceof Core.Read read && fields.containsKey(read.binding())) {
            out.add(fields.get(read.binding()));
        }
        Core.forEachChild(node, child -> readFrom(child, fields, out));
    }

    /** The field the place {@code e} is, or null where it is no field of this record. */
    RuleKey fieldAt(Core e) {
        return ElementsApart.placeOf(e, fields, true);
    }
}
