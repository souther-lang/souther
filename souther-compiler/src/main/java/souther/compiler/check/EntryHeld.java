package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.OrderedRuns;
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
import java.util.LinkedHashSet;
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

    private EntryHeld() {}

    /**
     * What a rule asks of a map beside a key, as the expressions it names them with.
     *
     * @param container what the map is written as
     * @param key       what the key is written as
     * @param valueIn   the numbers the value under the key is to be one of, at the places of it the
     *                  rule names, or null where the rule asks nothing of it
     */
    public record Stated(Core container, Core key, ValueAsked valueIn) {}

    /**
     * What a rule asks of the map at {@code container}: the place standing at the key, and the
     * numbers the value under it is to be one of, or null where nothing is asked of the value.
     */
    public record Requirement(RuleKey key, ValueAsked valueIn) {}

    /**
     * {@code clause} read as asking a map for an entry, or null where it asks nothing of the kind.
     *
     * @param followed what a name is given, for a name bound to a part of the clause; the
     *                 expression itself where it is not such a name
     * @param newtypes which names wear one value, for the places of the value a rule names
     */
    public static Stated read(Core clause, Function<Core, Core> followed,
                              DeclarationNewtypes newtypes) {
        Core here = Core.withoutStanding(followed.apply(Core.withoutStanding(clause)));
        Stated asked = membership(here, followed);
        if (asked != null) {
            return asked;
        }
        return here instanceof Core.Match match ? readMatch(match, followed, newtypes) : null;
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
    private static Stated readMatch(Core.Match match, Function<Core, Core> followed,
                                    DeclarationNewtypes newtypes) {
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
        if (AnOperationApplied.of(scrutinee) instanceof AnOperationApplied applied
                && applied.mapsAnOption() instanceof AnOperationApplied.Mapped mapped
                && Core.withoutStanding(present.body()) instanceof Core.Read read
                && read.binding().equals(payload.binder().binding())
                && Core.withoutStanding(mapped.closure()) instanceof Core.Block block
                && block.params().size() == 1
                && lookup(mapped.option()) instanceof AnOperationApplied.Lookup lookedUp) {
            ValueAsked is = valueIn(block.body(), block.params().getFirst().binding(), followed,
                    newtypes);
            return is == null ? null : new Stated(lookedUp.container(), lookedUp.key(), is);
        }
        // The lookup matched on directly, the present arm stating what the value is.
        if (lookup(scrutinee) instanceof AnOperationApplied.Lookup lookedUp) {
            ValueAsked is = valueIn(present.body(), payload.binder().binding(), followed,
                    newtypes);
            return is == null ? null : new Stated(lookedUp.container(), lookedUp.key(), is);
        }
        return null;
    }

    /** {@code e} as a lookup in a map, or null where it is not one. */
    private static AnOperationApplied.Lookup lookup(Core e) {
        AnOperationApplied applied = AnOperationApplied.of(e);
        return applied == null ? null : applied.lookup();
    }

    /**
     * The numbers {@code statement} says the value bound to {@code value} is one of, or null where
     * it says anything else of it.
     *
     * <p>Each statement the clause is made of, read as the shape reads it ({@link ClauseExpr}): a
     * comparison of the value with a written number, in either order, or the comparison of two
     * decimals written as the sign of their difference against nought, stated or denied. The
     * numbers they leave together are the ones every one of them leaves, so a conjunction is the
     * meet of its parts and a part of any other kind leaves the clause unread.
     */
    private static ValueAsked valueIn(Core statement, BindingId value,
                                      Function<Core, Core> followed, DeclarationNewtypes newtypes) {
        ValueAsked together = null;
        for (ConjunctStatements.Stated each
                : ConjunctStatements.statedBy(ClauseExpr.of(statement, true))) {
            ValueAsked one = valueInStated(StatedComparison.of(each.said()), value, followed,
                    newtypes);
            if (one == null) {
                return null;
            }
            together = together == null ? one : together.meet(one);
        }
        return together;
    }

    /** The numbers {@code stated} says the value bound to {@code value} is one of, at the place of
     *  it the comparison names, or null where it says anything else of it. */
    private static ValueAsked valueInStated(StatedComparison stated, BindingId value,
                                            Function<Core, Core> followed,
                                            DeclarationNewtypes newtypes) {
        if (stated == null) {
            return null;
        }
        // The sign of the difference of two numbers against nought, as a comparison of decimals is
        // written: it compares the two numbers the way it compares its answer with nought.
        if (AnOperationApplied.of(Core.withoutStanding(stated.left()))
                instanceof AnOperationApplied compared
                && compared.ordersItsArguments() instanceof AnOperationApplied.Ordered ordered
                && Core.withoutStanding(stated.right()) instanceof Core.Int nought
                && nought.value() == 0) {
            // The sign against nought is the greater against the lesser, whichever of the two
            // arguments the operation names as the greater.
            stated = new StatedComparison(stated.claim(), ordered.greater(), ordered.lesser(),
                    stated.reading());
        }
        StatedComparison.Numbered<List<String>> aboutTheValue =
                stated.at(side -> placeOfTheValue(side, value, newtypes));
        BigDecimal written = aboutTheValue == null ? null
                : writtenNumber(aboutTheValue.other(), followed);
        return written == null ? null
                : ValueAsked.at(aboutTheValue.number(), OrderedRuns.leftBy(
                        aboutTheValue.claim().statedRelation(), Count.of(written)));
    }

    /**
     * The place of the value bound to {@code value} that {@code e} is: the value itself, the value
     * a name wraps, or a field of it by the fields on the way. Null where {@code e} is no place of
     * it.
     */
    private static List<String> placeOfTheValue(Core e, BindingId value,
                                                DeclarationNewtypes newtypes) {
        Location at = Location.of(e, newtypes,
                binding -> binding.equals(value) ? Location.of(binding) : null,
                projection -> Location.stepsOf(projection, newtypes));
        return at == null ? null : at.path();
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
            Stated stated = entryOf(one, source.newtypes());
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

    /** What {@code one} asks a map for, or null where it asks nothing of the kind. */
    private static Stated entryOf(InvariantStatement one, DeclarationNewtypes newtypes) {
        return switch (one) {
            case InvariantStatement.HoldsAnEntry it -> it.held();
            case InvariantStatement.Applies it -> read(it.call(), core -> core, newtypes);
            case InvariantStatement.Compares _, InvariantStatement.Unread _,
                 InvariantStatement.BalancesSides _ -> null;
        };
    }

    /**
     * The maps of the record {@code named} that its rules ask for an entry no value of the map's
     * value type can be, by the place of the map.
     *
     * <p>A proof and not the absence of one. The rules of a record all hold, so a statement asking
     * for an entry that cannot stand is false of every value of the record, and the record has none:
     * the numbers a rule asks of the value under a key contradict the ones another asks of it, the
     * range its type leaves holds none of them, or the one it names is one the type refuses. A range
     * the type leaves holding several numbers none of which was found is no such proof
     * ({@link Among.NotFound}), and neither is a rule the record's other rules leave unread: the
     * statements read are every one of them required of the record, whatever else is not read.
     */
    public static Set<RuleKey> askingForNoEntry(TypeSymbol.AtModule named,
                                                RuleReadingContext world) {
        RecordRules rules = RecordRules.of(named, world.source());
        if (rules == null) {
            return Set.of();
        }
        Map<RuleKey, List<Requirement>> asked = new LinkedHashMap<>();
        for (InvariantStatement one : rules.statements()) {
            Stated stated = entryOf(one, world.source().newtypes());
            RuleKey where = stated == null ? null : rules.fieldAt(stated.container());
            RuleKey key = stated == null ? null : rules.fieldAt(stated.key());
            if (where != null && key != null) {
                asked.computeIfAbsent(where, _ -> new ArrayList<>())
                        .add(new Requirement(key, stated.valueIn()));
            }
        }
        Set<RuleKey> out = new LinkedHashSet<>();
        asked.forEach((map, requirements) -> {
            Type value = valueTypeOf(map, named, world.source());
            for (ValueAsked each : valuesAsked(requirements).values()) {
                if (each.holdsNothing()
                        || (value != null && numbersAmong(value, each, named, world)
                                instanceof Among.NoneExists)) {
                    out.add(map);
                }
            }
        });
        return Set.copyOf(out);
    }

    /** The type of the values the field {@code map} of {@code named} holds under its keys, or null
     *  where it is no map. */
    private static Type valueTypeOf(RuleKey map, TypeSymbol.AtModule named,
                                    RuleReadingSource source) {
        if (map.steps().size() != 1
                || !(TypeView.shapeOf(Type.ref(named), source.inners(), source.symbols(),
                        source.kinds(), source.sums()) instanceof Shape.Product(TypeSymbol _,
                        var fields))
                || !(fields.get(map.steps().getFirst()) instanceof Type mapType)
                || !(TypeView.of(mapType, source.inners(), source.symbols(), source.kinds(),
                        source.sums()).shape() instanceof Shape.Mapping(Type _, Type value))) {
            return null;
        }
        return value;
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
     * builders go by ({@link #numbersAmong}), since a key is free only where the entry can be
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
        Type value = valueTypeOf(map, named, world.source());
        if (value == null) {
            return false;
        }
        for (ValueAsked asked : valuesAsked(requirements).values()) {
            if (!(numbersAmong(value, asked, named, world) instanceof Among.Found)) {
                return false;
            }
        }
        return true;
    }

    /** What the names a position wears make of a number. */
    private enum Admission {
        /** It is among the position's values as far as the names say. */
        ADMITTED,
        /** The names refuse it: it is outside what they leave the position, which is a bound
         *  every value of it is inside. */
        REFUSED,
        /** Neither shown: a number this cannot write, or a position whose names ask the record
         *  being read. */
        NOT_SHOWN
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
     * <p>Not shown for a type that wears {@code within}, the record being read, where one is given:
     * asking its names asks the record, whose reading this is part of. And for a number this cannot
     * write as a count, which the names are then not asked about.
     */
    private static Admission admission(Type type, BigDecimal number, TypeSymbol.AtModule within,
                                       RuleReadingContext reading) {
        RuleReadingSource source = reading.source();
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        if (within != null && view.wrappers().contains(within)) {
            return Admission.NOT_SHOWN;
        }
        ExactRatio exact = ExactRatio.of(number);
        DeclaredBounds.Range own = DeclaredBounds.of(view, reading);
        if (own != null && !new NumericDomain.Bounds(own.min(), own.max()).admits(exact)) {
            return Admission.REFUSED;
        }
        Optional<Count> count = Count.written(exact).orNull();
        if (count == null || count.isEmpty()) {
            return Admission.NOT_SHOWN;
        }
        Value value = Value.number(count.get().at());
        for (TypeSymbol each : view.wrappers()) {
            if (each instanceof TypeSymbol.AtModule named
                    && !FieldDomains.of(named, reading).admits(RuleKey.THE_VALUE).approximation()
                            .has(value)) {
                return Admission.REFUSED;
            }
        }
        return Admission.ADMITTED;
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
        return valuesAsked(requirements).values().stream().noneMatch(ValueAsked::holdsNothing);
    }

    /**
     * The numbers every rule asking about a key leaves the value under it, by the key, for the
     * keys some rule asks anything of the value of.
     *
     * <p>A conjunction of what the rules ask: the numbers the rules leave together at each place,
     * which are none where they contradict one another.
     */
    public static Map<RuleKey, ValueAsked> valuesAsked(List<Requirement> requirements) {
        Map<RuleKey, ValueAsked> out = new LinkedHashMap<>();
        for (Requirement each : requirements) {
            if (each.valueIn() != null) {
                out.merge(each.key(), each.valueIn(), ValueAsked::meet);
            }
        }
        return out;
    }

    /**
     * Whether no value is what both {@code one} and {@code other} ask: two keys asked these of
     * their values are two entries, since one entry holds one value.
     */
    public static boolean leaveNoNumberInCommon(ValueAsked one, ValueAsked other) {
        return one.excludes(other);
    }

    /**
     * What a search for the numbers a value of a type can be at the places asked came to.
     *
     * <p>Three answers and not two, because what a reader does with the third is not what it does
     * with the second: a type that has no such number leaves the rules asking for it nothing to be
     * built from, which is a fact about the model, and one whose numbers this did not find says
     * only that this did not.
     */
    public sealed interface Among {

        /** The number found at each place asked. */
        record Found(Map<List<String>, BigDecimal> at) implements Among {

            public Found {
                at = Map.copyOf(at);
            }
        }

        /** There is none: what is asked and what the type leaves share no number at some place, or
         *  the one number they share is one the type refuses. */
        record NoneExists() implements Among {}

        /** None was found, and the numbers between the ones tried were not asked about. */
        record NotFound() implements Among {}
    }

    /**
     * A number at each place of {@code value} that {@code asked} names, which the type at the
     * place can be.
     *
     * <p>None exists where it does at any one place: the value is asked to be what no value of the
     * type is. Where none was found at some place and none is shown to be missing at another, none
     * was found.
     *
     * @param within the record being read, where one is given ({@link #admission})
     */
    public static Among numbersAmong(Type value, ValueAsked asked, TypeSymbol.AtModule within,
                                     RuleReadingContext reading) {
        Map<List<String>, BigDecimal> found = new LinkedHashMap<>();
        boolean notFound = false;
        for (Map.Entry<List<String>, OrderedRuns> each : asked.at().entrySet()) {
            Type there = typeAt(value, each.getKey(), reading.source());
            if (there == null) {
                notFound = true;
                continue;
            }
            switch (numberAmong(there, each.getValue(), within, reading)) {
                case Among.Found one -> found.put(each.getKey(), one.at().get(ValueAsked.THE_VALUE));
                case Among.NotFound _ -> notFound = true;
                case Among.NoneExists none -> {
                    return none;
                }
            }
        }
        return notFound ? new Among.NotFound() : new Among.Found(found);
    }

    /** The type standing at {@code place} of a value of {@code type}, or null where the type has
     *  no field there. */
    private static Type typeAt(Type type, List<String> place, RuleReadingSource source) {
        Type at = type;
        for (String field : place) {
            if (!(TypeView.of(at, source.inners(), source.symbols(), source.kinds(), source.sums())
                    .shape() instanceof Shape.Product(TypeSymbol _, var fields))
                    || !(fields.get(field) instanceof Type next)) {
                return null;
            }
            at = next;
        }
        return at;
    }

    /**
     * A number among {@code asked} that a value of {@code type} can be, which is a number and not
     * a record: the one place of it is the value itself.
     *
     * <p>Chosen among the numbers a range is entered by: its ends, a step inside each end, and the
     * middle. Each is held to the type's own rules ({@link #admission}), so a number the type
     * refuses is never the answer, and to the carrier's grain, so a whole-number type is offered
     * whole numbers only. A type whose rules leave a gap in the range that none of those numbers
     * is outside of is answered {@link Among.NotFound}, which says nothing is known and not that
     * no number will do. Where what is asked is one number, there is no other to find, and the
     * type's refusing it is the answer that none exists.
     *
     * @param within the record being read, where one is given ({@link #admission})
     */
    private static Among numberAmong(Type type, OrderedRuns asked, TypeSymbol.AtModule within,
                                     RuleReadingContext reading) {
        RuleReadingSource source = reading.source();
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        DeclaredBounds.Range own = DeclaredBounds.of(view, reading);
        OrderedRuns room = own == null ? asked
                : asked.meet(OrderedRuns.of(new OrderedInterval(own.min(), own.max())));
        boolean whole = view.shape() instanceof Shape.Scalar(Type.Prim prim)
                && prim == Type.Prim.INT;
        boolean noneInAnyRun = true;
        for (OrderedInterval run : room.runs()) {
            switch (numberAmong(type, new NumericDomain.Bounds(run.low(), run.high()), whole,
                    within, reading)) {
                case Among.Found found -> {
                    return found;
                }
                case Among.NotFound _ -> noneInAnyRun = false;
                case Among.NoneExists _ -> { }
            }
        }
        return noneInAnyRun ? new Among.NoneExists() : new Among.NotFound();
    }

    /** The same within one run of the numbers asked, where {@code whole} says the carrier holds
     *  whole numbers only. */
    private static Among numberAmong(Type type, NumericDomain.Bounds room, boolean whole,
                                     TypeSymbol.AtModule within, RuleReadingContext reading) {
        boolean refused = true;
        for (Count each : entering(room, whole)) {
            if (!room.admits(each)) {
                continue;
            }
            switch (admission(type, each.at(), within, reading)) {
                case ADMITTED -> {
                    return new Among.Found(Map.of(ValueAsked.THE_VALUE, each.at()));
                }
                case NOT_SHOWN -> refused = false;
                case REFUSED -> { }
            }
        }
        return refused && leavesOneNumber(room) ? new Among.NoneExists() : new Among.NotFound();
    }

    /** Whether {@code room} is one number, so that the refusal of the numbers tried is the
     *  refusal of every number in it. */
    private static boolean leavesOneNumber(NumericDomain.Bounds room) {
        if (room.min() == null || room.max() == null || !room.min().inclusive()
                || !room.max().inclusive() || !(room.min().at() instanceof Count low)
                || !(room.max().at() instanceof Count high)) {
            return false;
        }
        return low.exactly().equals(high.exactly());
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
