package souther.compiler.jvm;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A projection as an artifact recorded it: what it says under each label.
 *
 * <p>What a module on the path says it provides and what it says it was built against arrive as
 * these, and a projection this compilation works out is compared with one by what it records
 * ({@link #of}).
 *
 * <p>A record is what it says under each label and nothing else. Where the facts stand among each
 * other is how they are shown and written, and is not part of what two records are compared by: an
 * order that matters to a class — the fields a constructor takes in turn, the dependencies it is
 * handed — is written inside one fact's value. So whether two records are equal and where they
 * differ are read off one mapping, and two records that are not equal always differ under some
 * label ({@link #movedIn}).
 *
 * @param facts what each label says, in the order the projection lists them
 */
public record LinkageRecord(Map<String, String> facts) {

    public LinkageRecord {
        for (Map.Entry<String, String> fact : facts.entrySet()) {
            // What a report shows and an artifact writes, so neither half may be blank.
            if (fact.getKey() == null || fact.getKey().isEmpty() || fact.getValue() == null
                    || fact.getValue().isEmpty()) {
                throw new IllegalArgumentException("a fact has a label and a value: "
                        + fact.getKey() + " = " + fact.getValue());
            }
        }
        facts = Collections.unmodifiableMap(new LinkedHashMap<>(facts));
    }

    /** What an artifact records of {@code projection}. */
    public static LinkageRecord of(LinkageProjection projection) {
        Map<String, String> facts = new LinkedHashMap<>();
        for (LinkageProjection.Fact fact : projection.facts()) {
            if (facts.put(fact.label(), fact.value()) != null) {
                throw new IllegalStateException(projection.target().shown() + " says two things"
                        + " under `" + fact.label() + "`");
            }
        }
        return new LinkageRecord(facts);
    }

    /**
     * Where this and {@code now} differ, as a report shows it: each label whose fact is not the same
     * in both, with what this says under it and what {@code now} says, in the order this lists them
     * and then the labels only {@code now} has.
     *
     * <p>Empty exactly where the two are equal.
     */
    public List<Moved> movedIn(LinkageRecord now) {
        Set<String> labels = new LinkedHashSet<>(facts.keySet());
        labels.addAll(now.facts.keySet());
        List<Moved> moved = new ArrayList<>();
        for (String label : labels) {
            String was = facts.get(label);
            String is = now.facts.get(label);
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
}
