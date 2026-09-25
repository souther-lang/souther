package souther.compiler.jvm;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A projection as an artifact recorded it: its facts, in order.
 *
 * <p>What a module on the path says it provides and what it says it was built against arrive as
 * these, and a projection this compilation works out is compared with one by what it records
 * ({@link #of}). The facts are the whole of a projection's written form, so two of these are equal
 * exactly where the projections they record are.
 */
public record LinkageRecord(List<LinkageProjection.Fact> facts) {

    public LinkageRecord {
        facts = List.copyOf(facts);
        Set<String> labels = new LinkedHashSet<>();
        for (LinkageProjection.Fact fact : facts) {
            if (!labels.add(fact.label())) {
                throw new IllegalArgumentException("a projection records one fact under `"
                        + fact.label() + "`, and this records two");
            }
        }
    }

    /** What an artifact records of {@code projection}. */
    public static LinkageRecord of(LinkageProjection projection) {
        return new LinkageRecord(projection.facts());
    }

    /**
     * Where this and {@code now} differ, as a report shows it: each label whose fact is not the same
     * in both, with what this says under it and what {@code now} says, in the order this lists them
     * and then the labels only {@code now} has.
     */
    public List<Moved> movedIn(LinkageRecord now) {
        Map<String, String> mine = byLabel(facts);
        Map<String, String> theirs = byLabel(now.facts);
        Set<String> labels = new LinkedHashSet<>(mine.keySet());
        labels.addAll(theirs.keySet());
        List<Moved> moved = new ArrayList<>();
        for (String label : labels) {
            String was = mine.get(label);
            String is = theirs.get(label);
            if (was == null || !was.equals(is)) {
                moved.add(new Moved(label, was, is));
            }
        }
        return List.copyOf(moved);
    }

    /**
     * One fact that is not the same in two records.
     *
     * @param label what the fact is about
     * @param was   what the first says, or null where it says nothing under the label
     * @param now   what the second says, or null where it says nothing under the label
     */
    public record Moved(String label, String was, String now) {}

    private static Map<String, String> byLabel(List<LinkageProjection.Fact> facts) {
        Map<String, String> out = new LinkedHashMap<>();
        for (LinkageProjection.Fact fact : facts) {
            out.put(fact.label(), fact.value());
        }
        return out;
    }
}
