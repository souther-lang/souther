package souther.compiler.coverage;

import souther.compiler.types.SourceConstructOrigin;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.SequencedMap;
import java.util.Set;
import java.util.TreeMap;
import java.util.function.Predicate;

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
 * @param bySite every numbered arm that has a sibling, by its site, in the order of the sites
 */
public record ArmReplacements(SequencedMap<Integer, AtSite> bySite) {

    public ArmReplacements {
        bySite = Collections.unmodifiableSequencedMap(new TreeMap<>(bySite));
    }

    /** Nothing can be replaced: what a build that records nothing carries. */
    public static final ArmReplacements NONE = new ArmReplacements(new TreeMap<>());

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
     * Where two programs could answer differently, as far as the bodies say: the ways through one of
     * them whose answer is not the other's, each written as the arms it goes through.
     *
     * <p>Read off the source and nothing else, so it says where the two could part and never that
     * they do. A way the model's own rules prove nothing goes down is a way no input takes, so where
     * every way is one of those the two are one program under two spellings, and no row is owed for
     * telling them apart. That is a proof, and it is the only way this compiler concludes two
     * programs are the same: a search that found no input they part at shows nothing.
     *
     * @param always where some way parts them with no arm on it a proof could take away — an answer
     *               standing outside every fork, or more ways than this reads
     * @param ways   the ways that part them, where {@code always} is false; none where the two
     *               answer alike on every way there is
     */
    public record Differs(boolean always, List<List<ControlPlace.Arm>> ways) {

        public Differs {
            ways = always ? List.of() : ways.stream().map(List::copyOf).toList();
        }

        /** Parts them whatever the rules prove. */
        public static final Differs ALWAYS = new Differs(true, List.of());

        /** Parts them on no way at all. */
        public static final Differs NEVER = new Differs(false, List.of());

        /** Whether every way that parts them goes through an arm {@code unreached} answers for. */
        public boolean provenAway(Predicate<ControlPlace.Arm> unreached) {
            return !always && ways.stream().allMatch(way -> way.stream().anyMatch(unreached));
        }
    }

    /**
     * What one sibling comes to as a replacement.
     *
     * <p>Two cases, because a sibling the classes do not carry is still a rewrite an author could
     * make. Whether a row would notice it is then something this compiler could not find out, which
     * is not the same as there being nothing to notice. Both say where the sibling and the arm could
     * answer differently, which is what decides whether there is anything to notice at all.
     */
    public sealed interface Sibling {

        /** Where the sibling and the arm could answer differently. */
        Differs differs();

        /** The classes carry it, and a run can ask for it. */
        record Carried(Differs differs) implements Sibling {

            public Carried {
                Objects.requireNonNull(differs, "a sibling says where it parts from the arm");
            }
        }

        /** The classes do not carry it, and why. */
        record NotCarried(Why why, Differs differs) implements Sibling {

            public NotCarried {
                Objects.requireNonNull(why, "a sibling left out was left out for a reason");
                Objects.requireNonNull(differs, "a sibling says where it parts from the arm");
            }
        }

        /** Why a sibling is not carried. */
        enum Why {
            /**
             * Carrying the siblings would make the code larger than it may be: larger than this
             * compiler lets a fork grow by, or past what the JVM holds in the method the fork is
             * written in. A limit of the classes and not of the model.
             */
            TOO_LARGE
        }
    }

    /**
     * These replacements with nothing carried at {@code sites}: what the classes hold where the
     * emitter wrote the arms there without their siblings. A sibling the classes do not carry is
     * still a rewrite, left as one this could not put to a row and why.
     */
    public ArmReplacements carryingNothingAt(Set<Integer> sites) {
        SequencedMap<Integer, AtSite> out = new TreeMap<>();
        bySite.forEach((site, at) -> {
            if (!sites.contains(site)) {
                out.put(site, at);
                return;
            }
            Map<Integer, Sibling> siblings = new LinkedHashMap<>();
            at.siblings().forEach((with, sibling) -> siblings.put(with,
                    new Sibling.NotCarried(Sibling.Why.TOO_LARGE, sibling.differs())));
            out.put(site, new AtSite(at.fork(), at.part(), siblings));
        });
        return new ArmReplacements(out);
    }

    /**
     * Every site of arm {@code part} of {@code fork}, the arm an author wrote, in the order of the
     * sites. A helper spliced into several places is one arm at several sites, and a rewrite of it
     * is a rewrite at all of them at once.
     */
    public List<AtSite> ofArm(SourceConstructOrigin fork, int part) {
        return bySite.values().stream()
                .filter(at -> at.fork().equals(fork) && at.part() == part)
                .toList();
    }

    /**
     * The sites a run asks for to replace arm {@code part} of {@code fork} with arm {@code with}:
     * every site of that arm whose classes carry the sibling, each mapped to {@code with}.
     */
    public SequencedMap<Integer, Integer> replacing(SourceConstructOrigin fork, int part,
                                                    int with) {
        SequencedMap<Integer, Integer> sites = new LinkedHashMap<>();
        bySite.forEach((site, at) -> {
            if (at.fork().equals(fork) && at.part() == part
                    && at.siblings().get(with) instanceof Sibling.Carried) {
                sites.put(site, with);
            }
        });
        return sites;
    }
}
