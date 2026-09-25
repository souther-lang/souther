package souther.compiler.meta;

import souther.compiler.jvm.LinkageRecord;
import souther.compiler.jvm.LinkageTarget;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * Whether the classes of a compiled module link against the declarations a compilation has: each
 * declaration they were built against, held to what that declaration offers now.
 *
 * <p>Nothing here knows what a projection holds. Which facts a class links by is decided where a
 * projection is made, and this compares what was recorded with what is offered — so a fact a
 * projection comes to hold later is held here without a line of this changing.
 *
 * <p>Not {@link DeclarationAgreement}. That asks whether a value crossing between two builds is read
 * by the same declarations; this asks whether the symbolic references a class file carries resolve,
 * against the class files beside it, to what they resolved to when it was compiled. The two may read
 * the same declarations, and are different questions of them.
 */
public final class LinkageAgreement {

    private LinkageAgreement() {}

    /**
     * What holding the classes came to.
     *
     * @param disagreements each declaration they were built against that is not offered as it was
     * @param complete      whether every declaration they were built against could be held — false
     *                      where a module declaring one is not in the compilation, which is said
     *                      where that is found
     */
    public record Held(List<Disagreement> disagreements, boolean complete) {
        public Held {
            disagreements = List.copyOf(disagreements);
        }
    }

    /** A declaration the classes were built against that is not offered as it was. */
    public sealed interface Disagreement {

        /** The declaration. */
        LinkageTarget target();

        /** Its module declares nothing of its kind under its name. */
        record NotProvided(LinkageTarget target) implements Disagreement {}

        /** It is offered, and not as it was: {@code moved} is where, in the order it was recorded. */
        record Moved(LinkageTarget target, List<LinkageRecord.Moved> moved)
                implements Disagreement {
            public Moved {
                moved = List.copyOf(moved);
                if (moved.isEmpty()) {
                    throw new IllegalArgumentException(target.shown() + " is offered as it was");
                }
            }
        }
    }

    /**
     * Holds {@code required} to what each declaration's module offers.
     *
     * @param required   what the classes were built against, by the declaration
     * @param providedBy what a module offers, by the declaration — or null where the compilation
     *                   does not hold the module
     */
    public static Held of(Map<LinkageTarget, LinkageRecord> required,
                          Function<String, Map<LinkageTarget, LinkageRecord>> providedBy) {
        List<Disagreement> out = new ArrayList<>();
        boolean complete = true;
        for (Map.Entry<LinkageTarget, LinkageRecord> each : required.entrySet()) {
            LinkageTarget target = each.getKey();
            Map<LinkageTarget, LinkageRecord> offered = providedBy.apply(target.module());
            if (offered == null) {
                complete = false;
                continue;
            }
            LinkageRecord now = offered.get(target);
            if (now == null) {
                out.add(new Disagreement.NotProvided(target));
            } else if (!now.equals(each.getValue())) {
                out.add(new Disagreement.Moved(target, each.getValue().movedIn(now)));
            }
        }
        return new Held(out, complete);
    }
}
