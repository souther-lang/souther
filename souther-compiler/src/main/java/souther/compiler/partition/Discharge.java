package souther.compiler.partition;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * What became of each thing a run was asked for.
 *
 * <p>Keyed by the obligation itself, so what a reader joins a finding by is the identity the plan
 * used to ask. The entries used to carry that identity inside them as well and be held in a list,
 * which let one run hold an entry filed under one class whose value named another — and a reader
 * looking a class up by identity found whichever of the two the search wrote first.
 *
 * <p>Whether it covers the plan is {@link FillResult}'s to hold, since that is where the plan is.
 * This is the answers alone.
 *
 * <p>Nothing reads these in order. What a row is offered for is taken in the plan's order, and
 * everything else asks by key — so the order the entries were written in is kept for the sake of a
 * message about one run reading the same way twice, and is not something to build an answer from.
 */
public record Discharge(Map<Generator.ClassOwed, ClassDisposition> classes,
                        Map<Generator.ArmOwed, ArmDisposition> arms) {

    /** Nothing asked for and nothing answered, which is the only run this is right for. */
    public static final Discharge NOTHING = new Discharge(Map.of(), Map.of());

    public Discharge {
        classes = Collections.unmodifiableMap(new LinkedHashMap<>(classes));
        arms = Collections.unmodifiableMap(new LinkedHashMap<>(arms));
    }

    /** What became of one class, or null where this run was not asked about it. */
    public ClassDisposition at(Generator.ClassOwed owed) {
        return classes.get(owed);
    }

    /** What became of one arm, or null where this run was not asked about it. */
    public ArmDisposition at(Generator.ArmOwed owed) {
        return arms.get(owed);
    }
}
