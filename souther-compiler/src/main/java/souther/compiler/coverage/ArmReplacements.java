package souther.compiler.coverage;

import souther.compiler.types.SourceConstructOrigin;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;

/**
 * Which other arm's expression each numbered arm can be run with in its place.
 *
 * <p>What a row is asked to notice. A row that goes through an arm is evidence for it only where it
 * would answer differently had the arm been written as one of its siblings, and finding that out is
 * running the row again with the sibling's expression standing where the arm's is. The classes that
 * record where a run goes carry that sibling as well, behind a switch nothing turns on unless a run
 * asks for it ({@link Intervention}); this says, of every numbered arm, which siblings are there.
 *
 * <p>Keyed by the arm's site, because the site is what a run of the classes says it passed and what
 * the switch in the classes is asked by. Several sites are one arm where a helper is spliced into
 * several bodies, and the arm an author wrote is {@link AtSite#fork} and {@link AtSite#part}: a
 * replacement is of that arm, so it stands at every site of it at once, as an edit of the source
 * would.
 *
 * <p>A function of the bodies alone, as the numbering is. The emitter and whatever reads a run are
 * handed the same one, and a sibling one of them thinks is there and the other does not is a run
 * asked for something the classes cannot do.
 *
 * @param bySite every numbered arm that has a sibling, by its site
 */
public record ArmReplacements(Map<Integer, AtSite> bySite) {

    public ArmReplacements {
        bySite = Map.copyOf(bySite);
    }

    /** Nothing can be replaced: what a build that records nothing carries. */
    public static final ArmReplacements NONE = new ArmReplacements(Map.of());

    /**
     * One numbered arm and its siblings.
     *
     * @param fork     the fork the author wrote, which every site of this arm shares
     * @param part     which of the fork's arms this is
     * @param siblings each sibling that could stand in this arm's place, by its part, and whether
     *                 the classes carry it
     */
    public record AtSite(SourceConstructOrigin fork, int part, Map<Integer, Sibling> siblings) {

        public AtSite {
            Objects.requireNonNull(fork, "an arm is an arm of some fork");
            siblings = Map.copyOf(siblings);
            if (siblings.containsKey(part)) {
                throw new IllegalArgumentException("an arm is not its own sibling: part " + part
                        + " of " + fork);
            }
        }
    }

    /**
     * What one sibling comes to as a replacement.
     *
     * <p>Two cases, because a sibling the classes do not carry is still a rewrite an author could
     * make. Whether a row would notice it is then something this compiler could not find out, which
     * is not the same as there being nothing to notice.
     */
    public sealed interface Sibling {

        /** The classes carry it, and a run can ask for it. */
        record Carried() implements Sibling {}

        /** The classes do not carry it, and why. */
        record NotCarried(Why why) implements Sibling {

            public NotCarried {
                Objects.requireNonNull(why, "a sibling left out was left out for a reason");
            }
        }

        /** Why a sibling is not carried. */
        enum Why {
            /**
             * Carrying every sibling of the fork would make the code larger than this compiler lets
             * a fork grow by. A limit of the classes and not of the model.
             */
            TOO_LARGE
        }
    }

    /**
     * The sites a run asks for to replace arm {@code part} of {@code fork} with arm {@code with}:
     * every site of that arm whose classes carry the sibling, each mapped to {@code with}.
     */
    public Map<Integer, Integer> replacing(SourceConstructOrigin fork, int part, int with) {
        Map<Integer, Integer> sites = new LinkedHashMap<>();
        bySite.forEach((site, at) -> {
            if (at.fork().equals(fork) && at.part() == part
                    && at.siblings().get(with) instanceof Sibling.Carried) {
                sites.put(site, with);
            }
        });
        return sites;
    }
}
