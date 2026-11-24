package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.Shape;
import souther.compiler.check.ValueAsked;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The entries a map being composed is asked to hold, as keys and the values filed under them.
 *
 * <p>What the rules and the way ask of a map is a set of keys, each with the numbers the value
 * under it is to be among, or nothing of the value. The set is resolved here and nowhere else:
 * every demand on one key is one entry, the numbers asked of its value are the range every demand
 * leaves, and a number is written for the value by the same owner that writes it for a record's
 * map field ({@link Partitions#valueFiledAs}).
 *
 * <p>An entry the plan placed an element under is the one entry that some entry is, so every key
 * held for it is that key. Where the plan placed none, each key held is an entry of its own, over
 * whatever value the rules admit or the value they name.
 *
 * @param placed  the entry the plan's element is filed under, or null where there is none
 * @param others  each other entry asked for, with the value it is filed over where one is named
 * @param written the values written for the entries' values, which the map is to hold
 */
record EntriesAsked(Witnesses.Filed placed, List<Witnesses.Filed> others,
                    List<FixtureTemplate> written) {

    EntriesAsked {
        others = List.copyOf(others);
        written = List.copyOf(written);
    }

    /**
     * The entries {@code map} is asked to hold, or null where no map holds them: two keys held for
     * the one entry, numbers asked of a value that no number meets, or one a value of the map's
     * type cannot be.
     *
     * @param plannedKey the key the plan put its element under, or null
     * @param element    the element the plan placed, or null
     * @param keysHeld   keys asked of the one entry some entry is
     * @param eachFiled  keys each asked of an entry of their own
     */
    static EntriesAsked of(Shape.Mapping map, FixtureTemplate plannedKey, FixtureTemplate element,
                           List<ContainerContents.KeyAsked> keysHeld,
                           List<ContainerContents.KeyAsked> eachFiled,
                           RuleReadingContext reading) {
        Map<String, Wanted> held = wanted(keysHeld);
        Map<String, Wanted> each = wanted(eachFiled);
        if (held == null || each == null) {
            return null;
        }
        Map<String, Wanted> all = new LinkedHashMap<>(held);
        for (Wanted one : each.values()) {
            Wanted had = all.get(one.key().text());
            Wanted both = had == null ? one : had.meeting(one.range());
            if (both.contradictory()) {
                return null;
            }
            all.put(one.key().text(), both);
        }
        FixtureTemplate key = plannedKey;
        if (plannedKey != null || element != null) {
            for (Wanted one : held.values()) {
                if (key != null && !key.text().equals(one.key().text())) {
                    return null;
                }
                key = one.key();
            }
        }
        Wanted placedWants = key == null ? null : all.remove(key.text());
        List<FixtureTemplate> written = new ArrayList<>();
        FixtureTemplate placedValue = element;
        if (placedWants != null && placedWants.range() != null) {
            FixtureTemplate value = Partitions.valueFiledAs(map.value(), placedWants.range(),
                    reading);
            if (value == null || (element != null && !element.text().equals(value.text()))) {
                return null;
            }
            placedValue = value;
            written.add(value);
        }
        List<Witnesses.Filed> others = new ArrayList<>();
        for (Wanted one : all.values()) {
            FixtureTemplate value = null;
            if (one.range() != null) {
                value = Partitions.valueFiledAs(map.value(), one.range(), reading);
                if (value == null) {
                    return null;
                }
                written.add(value);
            }
            others.add(new Witnesses.Filed(one.key(), value));
        }
        return new EntriesAsked(key == null ? null : new Witnesses.Filed(key, placedValue),
                others, written);
    }

    /** A key and the numbers its value is asked to be among, or null where nothing is asked. */
    private record Wanted(FixtureTemplate key, ValueAsked range) {

        Wanted meeting(ValueAsked other) {
            return other == null ? this
                    : new Wanted(key, range == null ? other : range.meet(other));
        }

        /** Whether the demands on the key leave its value no number. */
        boolean contradictory() {
            return range != null && range.holdsNothing();
        }
    }

    /** Every demand on one key as one, by the key; null where the demands on a key leave its
     *  value no number. */
    private static Map<String, Wanted> wanted(List<ContainerContents.KeyAsked> asked) {
        Map<String, Wanted> out = new LinkedHashMap<>();
        for (ContainerContents.KeyAsked one : asked) {
            Wanted had = out.get(one.key().text());
            Wanted both = (had == null ? new Wanted(one.key(), null) : had)
                    .meeting(one.valueIn().orElse(null));
            if (both.contradictory()) {
                return null;
            }
            out.put(one.key().text(), both);
        }
        return out;
    }
}
