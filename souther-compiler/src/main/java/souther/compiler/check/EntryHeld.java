package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.Refinement;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;
import souther.compiler.values.Value;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
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
        return heldOn(named, source).requirements();
    }

    /**
     * The maps among {@link #writtenOn} that are built for whatever key is chosen: the keys
     * stand where their own places admit them, and the entries asked of the map are held for each.
     *
     * <p>Not what {@link #writtenOn} answers. That a map can be built holding the entries asked of
     * it is not that it can be for every key a key's own place admits: two entries asked of a map
     * that holds one, or of two keys one of which the record fixes, are entries no map holds
     * where the keys come together. The builders choose the keys apart and are right to offer what
     * they build; a reading that calls the key free is right only where no choice of keys is out
     * of the builders' reach, and for one key that is so whatever else stands.
     */
    public static Map<RuleKey, List<Requirement>> freelyKeyedOn(TypeSymbol.AtModule named,
                                                                RuleReadingContext world) {
        Held held = heldOn(named, world.source());
        Map<RuleKey, List<Requirement>> out = new LinkedHashMap<>();
        held.requirements().forEach((where, requirements) -> {
            if (keysStayFree(where, requirements, held.rules(), held.builtFor().get(where), named,
                    world)) {
                out.put(where, requirements);
            }
        });
        return Map.copyOf(out);
    }

    /** The maps built, the statements each was built for, and the rules they were read off. */
    private record Held(Map<RuleKey, List<Requirement>> requirements,
                        Map<RuleKey, List<InvariantStatement>> builtFor, RecordRules rules) {}

    private static Held heldOn(TypeSymbol.AtModule named, RuleReadingSource source) {
        RecordRules rules = RecordRules.of(named, source);
        // Only a record all of whose rules were read: a map is built holding the entries the rules
        // ask of it, and a rule nothing was made of may ask others, or ask the map something the
        // entries held would break.
        if (rules == null || !rules.readInFull()) {
            return new Held(Map.of(), Map.of(), rules);
        }
        Map<RuleKey, List<Requirement>> out = new LinkedHashMap<>();
        // The maps a rule was read of that the builders cannot keep: a rule they know the shape
        // of and cannot name the key of is as much a rule asking something of the map as one they
        // can.
        Set<RuleKey> notKept = new HashSet<>();
        Map<RuleKey, List<InvariantStatement>> builtFor = new HashMap<>();
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
                builtFor.computeIfAbsent(where, _ -> new ArrayList<>()).add(one);
            } else if (where != null) {
                notKept.add(where);
            }
        }
        Map<RuleKey, List<Requirement>> held = new LinkedHashMap<>();
        out.forEach((where, requirements) -> {
            // And a map no statement but those built for reads from: the map is built holding
            // what those ask of it, and a statement asking anything else of it, recognised or not
            // and however it is written, is one the map is built without knowing of.
            if (buildable(where, requirements) && !notKept.contains(where)
                    && !rules.readBesides(builtFor.get(where), where.steps().getFirst())) {
                held.put(where, List.copyOf(requirements));
            }
        });
        return new Held(Map.copyOf(held), Map.copyOf(builtFor), rules);
    }

    /**
     * Whether the map at {@code map} can be built holding the entries {@code requirements} ask of
     * it for every key the key's own place admits.
     *
     * <p>Proved for the one shape that can be, and left unanswered for every other: one entry asked
     * of the map, under one key, and nothing else asking anything of the map, how many it holds
     * included, since that is how many keys a type must have. Several keys come to one value, to
     * two the record does not allow beside each other, or to more values than their type has, and
     * that is a question about the keys together which a reading of each place alone cannot ask.
     * And a number asked of the value is held only if the value's type admits it, by the answer the
     * builders go by ({@link #valueTypeAdmits}), since a key is free only where the entry can be
     * written.
     */
    private static boolean keysStayFree(RuleKey map, List<Requirement> requirements,
                                        RecordRules rules, List<InvariantStatement> built,
                                        TypeSymbol.AtModule named, RuleReadingContext world) {
        Set<String> keys = new HashSet<>();
        for (Requirement each : requirements) {
            keys.add(each.key().steps().getFirst());
        }
        if (keys.size() != 1 || rules.readAtAll(built, map.steps().getFirst())) {
            return false;
        }
        RuleReadingSource source = world.source();
        if (!(TypeView.shapeOf(Type.ref(named), source.inners(), source.symbols(), source.kinds(),
                source.sums()) instanceof Shape.Product(TypeSymbol _, var fields))
                || !(fields.get(map.steps().getFirst()) instanceof Type mapType)
                || !(TypeView.of(mapType, source.inners(), source.symbols(), source.kinds(),
                        source.sums()).shape() instanceof Shape.Mapping(Type _, Type value))) {
            return false;
        }
        for (Requirement each : requirements) {
            if (each.valueIs() != null && !valueTypeAdmits(value, each.valueIs(), named, world)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Whether the names a position wears leave {@code number} among its values.
     *
     * <p>Asked of both the range the rules leave and the values they name: a type that admits a set
     * of numbers inside its range does not admit the others. What neither expresses is left to the
     * decoder, which refuses a number the rules refuse and says so; the values reading does not
     * read the arithmetic of a rule, so whether it read every rule says nothing here. The one
     * answer both the builders of a map and the reading of its keys go by, so a key is not called
     * free for an entry the builders cannot write.
     *
     * <p>False for a type that wears {@code within}, the record being read, where one is given:
     * asking its names asks the record, whose reading this is part of.
     */
    public static boolean valueTypeAdmits(Type type, BigDecimal number, TypeSymbol.AtModule within,
                                          RuleReadingContext reading) {
        RuleReadingSource source = reading.source();
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        if (within != null && view.wrappers().contains(within)) {
            return false;
        }
        ExactRatio exact = ExactRatio.of(number);
        DeclaredBounds.Range own = DeclaredBounds.of(view, reading);
        if (own != null && !new NumericDomain.Bounds(own.min(), own.max()).admits(exact)) {
            return false;
        }
        Optional<Count> count = Count.written(exact).orNull();
        if (count == null || count.isEmpty()) {
            return false;
        }
        Value value = Value.number(count.get().at());
        for (TypeSymbol each : view.wrappers()) {
            if (each instanceof TypeSymbol.AtModule named
                    && !FieldDomains.of(named, reading).admits(RuleKey.THE_VALUE).approximation()
                            .has(value)) {
                return false;
            }
        }
        return true;
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
