package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.Refinement;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * A rule saying the map at one place holds an entry under the key standing at another place, and
 * where it says so the value under the key.
 *
 * <p>Two forms are read: the membership test {@code Map.containsKey(key, map)}, and the lookup
 * {@code Map.get(key, map)} followed through {@code Option.map} and {@code Option.withDefault} to a
 * comparison of the value found with a written number, absent counting as false. Anything else
 * about the value found leaves the rule unread, since a builder told only that an entry exists
 * would build maps the rule refuses.
 *
 * <p>A fact about the key and the map together, which is what makes it a rule of the value they are
 * fields of and not of either: the map may hold any entries, and which of them the rule asks for
 * depends on what stands at the key.
 */
public final class EntryHeld {

    private static final ValueName.Stdlib.Operation GET = ValueName.Stdlib.operation("Map", "get");
    private static final ValueName.Stdlib.Operation CONTAINS_KEY =
            ValueName.Stdlib.operation("Map", "containsKey");
    private static final ValueName.Stdlib.Operation MAP =
            ValueName.Stdlib.operation("Option", "map");
    private static final ValueName.Stdlib.Operation COMPARE =
            ValueName.Stdlib.operation("Decimal", "compare");

    private EntryHeld() {}

    /**
     * What a rule asks of a map beside a key, as the expressions it names them with.
     *
     * @param container what the map is written as
     * @param key       what the key is written as
     * @param valueIs   the number the value under the key is to be, or null where the rule asks
     *                  nothing of it
     */
    public record Stated(Core container, Core key, BigDecimal valueIs) {}

    /**
     * What a rule asks of the map at {@code container}: the place standing at the key, and the
     * number the value under it is to be, or null where nothing is asked of the value.
     */
    public record Requirement(RuleKey key, BigDecimal valueIs) {}

    /**
     * {@code clause} read as asking a map for an entry, or null where it asks nothing of the kind.
     *
     * @param followed what a name is given, for a name bound to a part of the clause; the
     *                 expression itself where it is not such a name
     */
    public static Stated read(Core clause, Function<Core, Core> followed) {
        Core here = Core.withoutStanding(followed.apply(Core.withoutStanding(clause)));
        if (AnOperationApplied.of(here) instanceof AnOperationApplied(var operation, var args)
                && operation.equals(CONTAINS_KEY) && args.size() == 2) {
            return new Stated(args.get(1), args.get(0), null);
        }
        return here instanceof Core.Match match ? readMatch(match, followed) : null;
    }

    /** A match on what a lookup found, taking the absent arm as false. */
    private static Stated readMatch(Core.Match match, Function<Core, Core> followed) {
        Core.Case present = null;
        for (Core.Case arm : match.cases()) {
            if (!(arm.pattern() instanceof Core.ResolvedPattern.Single one)) {
                return null;
            }
            switch (one.selected().refinement()) {
                case Refinement.OptionPresent _ -> present = arm;
                case Refinement.OptionAbsent _ -> {
                    if (!(Core.withoutStanding(followed.apply(Core.withoutStanding(arm.body())))
                            instanceof Core.Bool no) || no.value()) {
                        return null;
                    }
                }
                case Refinement.Direct _ -> {
                    return null;
                }
            }
        }
        if (match.cases().size() != 2 || present == null
                || !(present.binding() instanceof Core.ArmBinding.Payload payload)) {
            return null;
        }
        Core scrutinee = Core.withoutStanding(followed.apply(Core.withoutStanding(match.scrutinee())));
        // The lookup mapped to a statement about the value, whose answer the present arm hands on.
        if (AnOperationApplied.of(scrutinee) instanceof AnOperationApplied(var operation, var args)
                && operation.equals(MAP) && args.size() == 2
                && Core.withoutStanding(present.body()) instanceof Core.Read read
                && read.binding().equals(payload.binder().binding())
                && Core.withoutStanding(args.getFirst()) instanceof Core.Block block
                && block.params().size() == 1
                && lookup(args.get(1)) instanceof AnOperationApplied(var _, var lookedUp)) {
            BigDecimal is = valueIs(block.body(), block.params().getFirst().binding(), followed);
            return is == null ? null : new Stated(lookedUp.get(1), lookedUp.get(0), is);
        }
        // The lookup matched on directly, the present arm stating what the value is.
        if (lookup(scrutinee) instanceof AnOperationApplied(var _, var lookedUp)) {
            BigDecimal is = valueIs(present.body(), payload.binder().binding(), followed);
            return is == null ? null : new Stated(lookedUp.get(1), lookedUp.get(0), is);
        }
        return null;
    }

    /** {@code e} as a lookup in a map, or null where it is not one. */
    private static AnOperationApplied lookup(Core e) {
        return AnOperationApplied.of(e) instanceof AnOperationApplied applied
                && applied.operation().equals(GET) && applied.args().size() == 2 ? applied : null;
    }

    /**
     * The number {@code statement} says the value bound to {@code value} is, or null where it says
     * anything else of it.
     */
    private static BigDecimal valueIs(Core statement, BindingId value,
                                      Function<Core, Core> followed) {
        if (!(Core.withoutStanding(statement) instanceof Core.Binary same)
                || same.op() != BinOp.EQ) {
            return null;
        }
        Core left = Core.withoutStanding(same.left());
        Core right = Core.withoutStanding(same.right());
        // A comparison of the two numbers that answers nought, as an equality of decimals is written.
        if (AnOperationApplied.of(left) instanceof AnOperationApplied(var operation, var args)
                && operation.equals(COMPARE) && args.size() == 2
                && right instanceof Core.Int nought && nought.value() == 0) {
            BigDecimal first = writtenNumber(args.get(1), followed);
            BigDecimal second = writtenNumber(args.get(0), followed);
            if (isTheValue(args.get(0), value) && first != null) {
                return first;
            }
            return isTheValue(args.get(1), value) ? second : null;
        }
        BigDecimal written = writtenNumber(right, followed);
        if (isTheValue(left, value) && written != null) {
            return written;
        }
        written = writtenNumber(left, followed);
        return isTheValue(right, value) ? written : null;
    }

    /** Whether {@code e} is the value bound to {@code value}, or the value a name wraps. */
    private static boolean isTheValue(Core e, BindingId value) {
        return switch (Core.withoutStanding(e)) {
            case Core.Read read -> read.binding().equals(value);
            case Core.FieldAccess access -> access.field().equals("value")
                    && Core.withoutStanding(access.target()) instanceof Core.Read read
                    && read.binding().equals(value);
            default -> false;
        };
    }

    /** The number {@code e} is, read through the names bound to it, or null where it is none. */
    private static BigDecimal writtenNumber(Core e, Function<Core, Core> followed) {
        return switch (Core.withoutStanding(followed.apply(Core.withoutStanding(e)))) {
            case Core.Decimal decimal -> decimal.value();
            case Core.Int whole -> BigDecimal.valueOf(whole.value());
            default -> null;
        };
    }

    /**
     * What the rules written on {@code named} ask of the map at each place, by the place.
     *
     * <p>Read off what each rule states ({@link InvariantStatements}), so a rule stated through a
     * helper is the rule written out. A rule whose key or map is not a field of the declaration is
     * left out: nothing builds for a rule it cannot name the places of.
     */
    public static Map<RuleKey, List<Requirement>> writtenOn(TypeSymbol.AtModule named,
                                                            RuleReadingSource source) {
        RecordRules rules = RecordRules.of(named, source);
        if (rules == null) {
            return Map.of();
        }
        Map<RuleKey, List<Requirement>> out = new LinkedHashMap<>();
        for (InvariantStatement one : rules.statements()) {
            Stated stated = switch (one) {
                case InvariantStatement.HoldsAnEntry it -> it.held();
                case InvariantStatement.Applies it -> read(it.call(), core -> core);
                case InvariantStatement.Compares _, InvariantStatement.Unread _,
                     InvariantStatement.BalancesSides _ -> null;
            };
            RuleKey where = stated == null ? null : rules.fieldAt(stated.container());
            RuleKey key = stated == null ? null : rules.fieldAt(stated.key());
            if (where != null && key != null) {
                out.computeIfAbsent(where, _ -> new ArrayList<>())
                        .add(new Requirement(key, stated.valueIs()));
            }
        }
        Map<RuleKey, List<Requirement>> held = new LinkedHashMap<>();
        out.forEach((where, requirements) -> {
            if (buildable(where, requirements)) {
                held.put(where, List.copyOf(requirements));
            }
        });
        return Map.copyOf(held);
    }

    /**
     * Whether a map can be built holding every entry {@code requirements} ask of it.
     *
     * <p>The one answer to what the builders of a record can keep, which is what a rule must be
     * for a reading to call it read: a rule the builders cannot keep is a rule left to the decoder
     * that runs it. The map and every key are fields of the record, since the builders choose a
     * record's fields one at a time and a key is chosen before the map it is a key of; and one
     * key is not asked for two numbers, since no map holds two values under it.
     */
    private static boolean buildable(RuleKey map, List<Requirement> requirements) {
        if (map.steps().size() != 1) {
            return false;
        }
        Map<RuleKey, BigDecimal> valueUnder = new HashMap<>();
        for (Requirement each : requirements) {
            if (each.key().steps().size() != 1 || each.key().equals(map)) {
                return false;
            }
            if (each.valueIs() != null) {
                BigDecimal had = valueUnder.putIfAbsent(each.key(), each.valueIs());
                if (had != null && had.compareTo(each.valueIs()) != 0) {
                    return false;
                }
            }
        }
        return true;
    }
}
