package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.semantics.MapPart;
import souther.compiler.types.BindingId;
import souther.compiler.types.Refinement;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;
import souther.compiler.values.Value;

import java.math.BigDecimal;
import java.math.BigInteger;
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
 * <p>Two forms are read: a membership test of the map's keys, as the library's laws say one is
 * ({@code Map.containsKey(key, map)}, {@code List.contains(key, Map.keys(map))}), and the lookup
 * {@code Map.get(key, map)} followed through {@code Option.map} and {@code Option.withDefault} to a
 * comparison of the value found with a written number ({@code ==}, {@code <}, {@code <=},
 * {@code >}, {@code >=}), absent counting as false. Anything else about the value found leaves the
 * rule unread, since a builder told only that an entry exists would build maps the rule refuses.
 *
 * <p>A fact about the key and the map together, which is what makes it a rule of the value they are
 * fields of and not of either: the map may hold any entries, and which of them the rule asks for
 * depends on what stands at the key.
 */
public final class EntryHeld {

    private static final ValueName.Stdlib.Operation GET = ValueName.Stdlib.operation("Map", "get");
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
     * @param valueIn   the numbers the value under the key is to be one of, as a range (one number
     *                  being the range of that number), or null where the rule asks nothing of it
     */
    public record Stated(Core container, Core key, NumericDomain.Bounds valueIn) {}

    /**
     * What a rule asks of the map at {@code container}: the place standing at the key, and the
     * numbers the value under it is to be one of, or null where nothing is asked of the value.
     */
    public record Requirement(RuleKey key, NumericDomain.Bounds valueIn) {}

    /**
     * {@code clause} read as asking a map for an entry, or null where it asks nothing of the kind.
     *
     * @param followed what a name is given, for a name bound to a part of the clause; the
     *                 expression itself where it is not such a name
     */
    public static Stated read(Core clause, Function<Core, Core> followed) {
        Core here = Core.withoutStanding(followed.apply(Core.withoutStanding(clause)));
        Stated asked = membership(here, followed);
        if (asked != null) {
            return asked;
        }
        return here instanceof Core.Match match ? readMatch(match, followed) : null;
    }

    /**
     * {@code e} read as asking whether a map holds a key, or null where it asks nothing of the kind.
     *
     * <p>As the library's laws say it and not by name: an operation true exactly where some key of
     * the map it is handed is the value beside ({@code Map.containsKey}), and one true exactly where
     * some element of a list is the value ({@code List.contains}) asked of a list of a map's keys
     * ({@code Map.keys}). The two are one question about the map.
     */
    private static Stated membership(Core e, Function<Core, Core> followed) {
        if (!(AnOperationApplied.of(e) instanceof AnOperationApplied applied)
                || !(applied.operation() instanceof ValueName.Stdlib.Operation operation)) {
            return null;
        }
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        AddsWhatItDoesNotHold.Asked byKey =
                facts.askedWhetherItHolds(operation, AddsWhatItDoesNotHold.Of.KEYS);
        if (byKey != null) {
            Core map = applied.argument(byKey.container());
            Core key = applied.argument(byKey.value());
            return map == null || key == null ? null : new Stated(map, key, null);
        }
        AddsWhatItDoesNotHold.Asked byElement =
                facts.askedWhetherItHolds(operation, AddsWhatItDoesNotHold.Of.ELEMENTS);
        Core list = byElement == null ? null : applied.argument(byElement.container());
        AnOperationApplied listed = list == null ? null
                : AnOperationApplied.of(followed.apply(Core.withoutStanding(list)));
        BoundOperationFacts.Listed part = listed == null ? null
                : facts.listsAPartOf(listed.operation());
        if (part == null || part.part() != MapPart.KEYS) {
            return null;
        }
        Core map = listed.argument(part.map());
        Core key = applied.argument(byElement.value());
        return map == null || key == null ? null : new Stated(map, key, null);
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
            NumericDomain.Bounds is =
                    valueIn(block.body(), block.params().getFirst().binding(), followed);
            return is == null ? null : new Stated(lookedUp.get(1), lookedUp.get(0), is);
        }
        // The lookup matched on directly, the present arm stating what the value is.
        if (lookup(scrutinee) instanceof AnOperationApplied(var _, var lookedUp)) {
            NumericDomain.Bounds is =
                    valueIn(present.body(), payload.binder().binding(), followed);
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
     * The numbers {@code statement} says the value bound to {@code value} is one of, or null where
     * it says anything else of it.
     *
     * <p>A comparison of the value with a written number, in either order, or the comparison of two
     * decimals written as the sign of their difference against nought. Not {@code !=}: the numbers
     * it leaves are not one range.
     */
    private static NumericDomain.Bounds valueIn(Core statement, BindingId value,
                                                Function<Core, Core> followed) {
        StatedComparison stated = Core.withoutStanding(statement) instanceof Core.Binary compares
                ? StatedComparison.of(compares, true) : null;
        if (stated == null) {
            return null;
        }
        // The sign of the difference of two numbers against nought, as a comparison of decimals is
        // written: it compares the two numbers the way it compares its answer with nought.
        if (AnOperationApplied.of(Core.withoutStanding(stated.left()))
                instanceof AnOperationApplied(var operation, var args)
                && operation.equals(COMPARE) && args.size() == 2
                && Core.withoutStanding(stated.right()) instanceof Core.Int nought
                && nought.value() == 0) {
            stated = new StatedComparison(stated.claim(), args.get(0), args.get(1),
                    stated.reading());
        }
        StatedComparison.Numbered<Boolean> aboutTheValue =
                stated.at(side -> isTheValue(side, value) ? Boolean.TRUE : null);
        BigDecimal written = aboutTheValue == null ? null
                : writtenNumber(aboutTheValue.other(), followed);
        OrderedInterval left = written == null ? null
                : OrderedInterval.leftBy(aboutTheValue.claim().statedRelation(), Count.of(written));
        return left == null ? null : new NumericDomain.Bounds(left.low(), left.high());
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
                        .add(new Requirement(key, stated.valueIn()));
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
        for (NumericDomain.Bounds asked : valuesAsked(requirements).values()) {
            if (numberIn(value, asked, named, world) == null) {
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
     * record's fields one at a time and a key is chosen before the map it is a key of; and the
     * rules asking about one key leave some number to the value under it, since no map holds two
     * values under a key.
     */
    private static boolean buildable(RuleKey map, List<Requirement> requirements) {
        if (map.steps().size() != 1) {
            return false;
        }
        for (Requirement each : requirements) {
            if (each.key().steps().size() != 1 || each.key().equals(map)) {
                return false;
            }
        }
        return valuesAsked(requirements).values().stream()
                .allMatch(NumericDomain.Bounds::holdsAValue);
    }

    /**
     * The numbers every rule asking about a key leaves the value under it, by the key, for the
     * keys some rule asks anything of the value of.
     *
     * <p>A conjunction of what the rules ask: the range the rules leave together, which holds no
     * number where they contradict one another.
     */
    public static Map<RuleKey, NumericDomain.Bounds> valuesAsked(List<Requirement> requirements) {
        Map<RuleKey, NumericDomain.Bounds> out = new LinkedHashMap<>();
        for (Requirement each : requirements) {
            if (each.valueIn() != null) {
                out.merge(each.key(), each.valueIn(), NumericDomain.Bounds::meet);
            }
        }
        return out;
    }

    /**
     * Whether no value is among both {@code one} and {@code other}: two keys asked these of their
     * values are two entries, since one entry holds one value.
     */
    public static boolean leaveNoNumberInCommon(NumericDomain.Bounds one,
                                                NumericDomain.Bounds other) {
        return !one.meet(other).holdsAValue();
    }

    /**
     * A number among {@code asked} that a value of {@code type} can be, or null where there is
     * none this finds.
     *
     * <p>Chosen among the numbers a range is entered by: its ends, a step inside each end, and the
     * middle. Each is held to the type's own rules ({@link #valueTypeAdmits}), so a number the
     * type refuses is never the answer, and to the carrier's grain, so a whole-number type is
     * offered whole numbers only. A type whose rules leave a gap in the range that none of those
     * numbers is outside of is answered null, which says nothing is known and not that no number
     * will do.
     *
     * @param within the record being read, where one is given ({@link #valueTypeAdmits})
     */
    public static BigDecimal numberIn(Type type, NumericDomain.Bounds asked,
                                      TypeSymbol.AtModule within, RuleReadingContext reading) {
        RuleReadingSource source = reading.source();
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        DeclaredBounds.Range own = DeclaredBounds.of(view, reading);
        NumericDomain.Bounds room = own == null ? asked
                : asked.meet(new NumericDomain.Bounds(own.min(), own.max()));
        if (!room.holdsAValue()) {
            return null;
        }
        boolean whole = view.shape() instanceof Shape.Scalar(Type.Prim prim)
                && prim == Type.Prim.INT;
        for (Count each : entering(room, whole)) {
            if (room.admits(each) && valueTypeAdmits(type, each.at(), within, reading)) {
                return each.at();
            }
        }
        return null;
    }

    /** The numbers a range is entered by, nearest the ends first. */
    private static List<Count> entering(NumericDomain.Bounds room, boolean whole) {
        Count low = room.min() != null && room.min().at() instanceof Count count ? count : null;
        Count high = room.max() != null && room.max().at() instanceof Count count ? count : null;
        List<Count> out = new ArrayList<>();
        out.add(low);
        out.add(high);
        out.add(low == null ? null : low.plus(1));
        out.add(high == null ? null : high.minus(1));
        out.add(low == null || high == null ? null : midway(low, high));
        if (low == null && high == null) {
            out.add(Count.of(0));
            out.add(Count.of(1));
        }
        return out.stream().filter(each -> each != null && (!whole || each.exactly().isWhole()))
                .distinct().toList();
    }

    /** The count halfway between two, or null where no count is. */
    private static Count midway(Count low, Count high) {
        if (!(low.exactly().plus(high.exactly()) instanceof ExactAnswer.Held<ExactRatio> sum)
                || !(sum.value().times(ExactRatio.of(BigInteger.ONE, BigInteger.TWO))
                        instanceof ExactAnswer.Held<ExactRatio> half)
                || !(Count.written(half.value())
                        instanceof ExactAnswer.Held<Optional<Count>> count)) {
            return null;
        }
        return count.value().orElse(null);
    }
}
