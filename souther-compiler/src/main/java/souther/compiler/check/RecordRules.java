package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BindingId;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.Collection;
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
 * @param readings         the fields each statement reads from, other than to count what a field
 *                         holds
 * @param countBoundedAbove the fields a rule leaves no more than some number of entries
 */
record RecordRules(Map<BindingId, String> fields, List<InvariantStatement> statements,
                   int declared, int unread, boolean everyRuleReached,
                   List<Reading> readings, Set<String> countBoundedAbove) {

    /**
     * Whether a rule of the record leaves the field no more than some number of entries, which
     * is what makes the entries a rule asks of it more than it can hold where they are all apart.
     */
    boolean countIsBoundedAbove(String field) {
        return countBoundedAbove.contains(field);
    }

    /** A statement and the fields of the record it reads from, whether or not it was recognised. */
    record Reading(InvariantStatement statement, Set<String> fields, Set<String> counted) {}

    /**
     * Whether a statement other than {@code built} reads from the field {@code field} in any way,
     * how many it holds included.
     *
     * <p>The question for a field that is a value and not a container the statements were built
     * for. That a bound on how many a field holds is the range its count already carries is true
     * of a container, whose builder is handed the range; the length of a key is the key's own
     * value, and a bound on it says which keys there are.
     */
    boolean readAtAll(Collection<InvariantStatement> built, String field) {
        for (Reading each : readings) {
            if ((each.fields().contains(field) || each.counted().contains(field))
                    && !built.contains(each.statement())) {
                return true;
            }
        }
        return false;
    }

    /**
     * Whether a statement other than {@code built} reads from the field {@code field}, other than
     * to count what it holds.
     *
     * <p>The question a builder asks before it takes a field on: it builds the field holding what
     * the statements it built for ask of it, and is right only if no other statement asks anything
     * else of the field. That a statement was recognised is not that it was built for, so the
     * builder names the ones it built for and every other is read from where it reads, whatever it
     * says: a denial, a denied choice, a rule written through a helper and a rule of a shape the
     * builder knows and could not place are all the same to it. How many a field holds is the count
     * the range of its values already carries, so a statement reading the field only through that
     * is no other statement.
     */
    boolean readBesides(Collection<InvariantStatement> built, String field) {
        for (Reading each : readings) {
            if (each.fields().contains(field) && !built.contains(each.statement())) {
                return true;
            }
        }
        return false;
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
        // Where every statement reads from, whatever it says and whether or not it was recognised.
        List<Reading> readings = new ArrayList<>();
        Set<String> boundedAbove = new HashSet<>();
        for (InvariantStatement one : statements) {
            Set<String> reads = new HashSet<>();
            Set<String> counted = new HashSet<>();
            switch (one) {
                case InvariantStatement.Unread it -> {
                    // A comparison the calls-only reading made nothing of is still a comparison,
                    // asked under the polarity it stood at.
                    StatedComparison compares =
                            Core.withoutStanding(it.said()) instanceof Core.Binary bin
                                    ? StatedComparison.of(bin, it.positive()) : null;
                    if (compares != null) {
                        readFromComparison(compares, fields, reads, counted, boundedAbove);
                    } else {
                        readFrom(it.said(), fields, reads);
                    }
                }
                case InvariantStatement.Compares it ->
                        readFromComparison(it.states(), fields, reads, counted, boundedAbove);
                case InvariantStatement.Applies it -> readFrom(it.call(), fields, reads);
                case InvariantStatement.HoldsAnEntry it -> {
                    readFrom(it.held().container(), fields, reads);
                    readFrom(it.held().key(), fields, reads);
                }
                case InvariantStatement.BalancesSides it -> readFrom(it.balanced().list(), fields,
                        reads);
            }
            readings.add(new Reading(one, Set.copyOf(reads), Set.copyOf(counted)));
        }
        return new RecordRules(Map.copyOf(fields), List.copyOf(statements), declared, unread,
                everyRuleReached, List.copyOf(readings), Set.copyOf(boundedAbove));
    }

    /**
     * The fields of the record a comparison reads, other than as a bound on how many a field holds.
     *
     * <p>Only a comparison of the count of a field itself with a number the record does not
     * decide, by an order, is the interval the range of the field's count already carries. Every
     * other statement about a count is read from the field: one that is not an interval
     * ({@code Map.size(rates) != 1}, {@code Int.floorMod(Map.size(rates), 2) == 1}), one that
     * relates the count to another field, and a count of a container made from the field
     * ({@code Map.size(Map.remove(0, rates))}), which depends on what the field holds.
     */
    private static void readFromComparison(StatedComparison states,
                                           Map<BindingId, String> fields, Set<String> out,
                                           Set<String> counted, Set<String> boundedAbove) {
        Set<String> left = new HashSet<>();
        Set<String> right = new HashSet<>();
        readFrom(states.left(), fields, left);
        readFrom(states.right(), fields, right);
        Rel rel = states.relationUnder(true);
        boolean countOnTheLeft = isTheCountOfAField(states.left(), fields) && right.isEmpty();
        boolean countOnTheRight = isTheCountOfAField(states.right(), fields) && left.isEmpty();
        if (rel == Rel.NE || !(countOnTheLeft || countOnTheRight)) {
            out.addAll(left);
            out.addAll(right);
            return;
        }
        counted.addAll(countOnTheLeft ? left : right);
        // Counted from the count's side, a bound from below is the only one that leaves room.
        Rel fromTheCount = countOnTheLeft ? rel : rel.turned();
        if (fromTheCount != Rel.GE && fromTheCount != Rel.GT) {
            boundedAbove.addAll(countOnTheLeft ? left : right);
        }
    }

    /** Whether {@code e} is a count taken of a field of the record itself. */
    private static boolean isTheCountOfAField(Core e, Map<BindingId, String> fields) {
        return Core.withoutStanding(e) instanceof Core.PreservedCall call
                && NumericMeasures.isMeasure(call.operation())
                && !call.args().isEmpty()
                && call.args().stream().allMatch(arg -> Core.withoutStanding(arg)
                        instanceof Core.Read read && fields.containsKey(read.binding()));
    }

    /** The fields of the record {@code e} reads. */
    private static void readFrom(Core e, Map<BindingId, String> fields, Set<String> out) {
        Core node = Core.withoutStanding(e);
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
