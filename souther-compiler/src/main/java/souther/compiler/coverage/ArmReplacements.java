package souther.compiler.coverage;

import souther.compiler.observe.Figure;
import souther.compiler.types.SourceConstructOrigin;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.SequencedMap;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
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

        /**
         * Why a sibling is not carried: carrying the siblings would make the code larger than it
         * may be. A limit of the classes and not of the model, and one of two limits that a wider
         * run does not treat alike.
         */
        sealed interface Why {

            /**
             * Larger than this compiler lets a fork grow by, which is a figure of its own: a run
             * allowing a fork more carries the sibling.
             *
             * @param limit what a fork may carry, as it stood where the fork was compared against
             *              it
             */
            record PastWhatAForkCarries(Figure limit) implements Why {

                public PastWhatAForkCarries {
                    Objects.requireNonNull(limit, "a fork held back was held to some figure");
                }
            }

            /**
             * Past what the JVM holds in the method the fork is written in. The host's limit and
             * not this compiler's, so a run allowing more of everything writes the method without
             * the sibling again.
             */
            record PastWhatAMethodHolds() implements Why {}
        }
    }

    /**
     * These replacements with nothing carried at {@code sites}: what the classes hold where the
     * emitter wrote the arms there without their siblings, because the method they are in would
     * otherwise be more than the JVM holds. A sibling the classes do not carry is still a rewrite,
     * left as one this could not put to a row and why.
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
                    new Sibling.NotCarried(new Sibling.Why.PastWhatAMethodHolds(),
                            sibling.differs())));
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

    /**
     * One rewrite a run can be asked for: arm {@code part} of {@code fork} answering as its sibling
     * {@code with}, at {@code replacing}'s sites ({@link #replacing}).
     */
    public record Rewrite(SourceConstructOrigin fork, int part, int with,
                          SequencedMap<Integer, Integer> replacing) implements RunRewrite {

        public Rewrite {
            Objects.requireNonNull(fork, "an arm is an arm of some fork");
            replacing = Collections.unmodifiableSequencedMap(new TreeMap<>(replacing));
        }

        @Override
        public Rewriting asked() {
            return Rewriting.ofArms(replacing);
        }
    }

    /**
     * These rewrites at the sites {@code kept} says yes to, and at no other.
     *
     * <p>Asked by the plan, which holds the numbering a site number is a place under. An arm
     * written once stands at as many sites as the behaviors that reach it have, and what is shown
     * of a rewrite — the ways nothing arrives at, the rows that went through — is shown of the sites
     * of one behavior ({@link CoverageSites.Plan#keepingTheArmsOf}).
     */
    ArmReplacements keeping(Predicate<Integer> kept) {
        SequencedMap<Integer, AtSite> out = new TreeMap<>();
        bySite.forEach((site, at) -> {
            if (kept.test(site)) {
                out.put(site, at);
            }
        });
        return new ArmReplacements(out);
    }

    /**
     * Every rewrite a run that went through {@code sites} can be run under: each sibling the
     * classes carry at one of those sites, once per arm and sibling however many of its sites the
     * run passed, in the order of the sites and then of the siblings.
     *
     * <p>What a recording is run again under, which is more than a row is asked
     * ({@link #askedOfARun}): a sibling some other site of the arm does not carry, and one that is
     * the arm under another spelling, are run here too. The runs are made before the rows are read
     * and before anything proves a way is never taken, and every rewrite a row is asked has to
     * have a run among them.
     */
    public List<Rewrite> through(Set<Integer> sites) {
        List<Rewrite> out = new ArrayList<>();
        Set<OfAnArm> seen = new HashSet<>();
        for (int site : new TreeSet<>(sites)) {
            AtSite at = bySite.get(site);
            if (at == null) {
                continue;
            }
            for (int with : new TreeSet<>(at.siblings().keySet())) {
                if (at.siblings().get(with) instanceof Sibling.Carried
                        && seen.add(new OfAnArm(at.fork(), at.part(), with))) {
                    out.add(new Rewrite(at.fork(), at.part(), with,
                            replacing(at.fork(), at.part(), with)));
                }
            }
        }
        return List.copyOf(out);
    }

    /** One rewrite of one arm, apart from where it is run. */
    private record OfAnArm(SourceConstructOrigin fork, int part, int with) {}

    /** What one rewrite of an arm comes to as a question a row through the arm is asked. */
    public sealed interface Asked {

        /** The sibling the arm is rewritten as. */
        int with();

        /** It can be run, at every site of the arm, as {@code rewrite}. */
        record Runs(Rewrite rewrite) implements Asked {

            @Override
            public int with() {
                return rewrite.with();
            }
        }

        /**
         * Some site of the arm does not carry the sibling, so no run is the rewrite: a run at the
         * sites that do is a program the author could not write.
         */
        record NotRun(int with, Sibling.Why why) implements Asked {}
    }

    /**
     * Every rewrite of arm {@code part} of {@code fork} that is another program, and what each comes
     * to as a question: in the order of the siblings.
     *
     * <p>A rewrite stands at every site of the arm at once, so it is the arm under another spelling
     * only where it is at each of them: where every site either lacks the sibling or has it proven
     * to part from the arm only on ways {@code unreached} answers for. And it can be run only where
     * every site having the sibling carries it.
     *
     * <p>The one answer to which rewrites a row through the arm is asked, whoever asks: the measure
     * of the rows written and the composer choosing a row to offer put the same questions.
     */
    public List<Asked> askedOf(SourceConstructOrigin fork, int part,
                               Predicate<ControlPlace.Arm> unreached) {
        List<AtSite> sites = ofArm(fork, part);
        Set<Integer> withs = new TreeSet<>();
        sites.forEach(at -> withs.addAll(at.siblings().keySet()));
        List<Asked> out = new ArrayList<>();
        for (int with : withs) {
            if (sites.stream().allMatch(at -> !at.siblings().containsKey(with)
                    || at.siblings().get(with).differs().provenAway(unreached))) {
                continue;
            }
            Sibling.Why left = null;
            for (AtSite at : sites) {
                if (left == null
                        && at.siblings().get(with) instanceof Sibling.NotCarried(var why, var _)) {
                    left = why;
                }
            }
            out.add(left != null ? new Asked.NotRun(with, left)
                    : new Asked.Runs(new Rewrite(fork, part, with, replacing(fork, part, with))));
        }
        return List.copyOf(out);
    }

    /**
     * The rewrites a row whose run is {@code run} is asked and can be run under: those of each arm
     * of {@code arms} the run was recorded at ({@link #askedOf}), once per arm and sibling, in the
     * order of {@code arms} and then of the siblings.
     */
    public List<Rewrite> askedOfARun(List<CoverageSites.ArmSite> arms, AlignedObservation run,
                                     Predicate<ControlPlace.Arm> unreached) {
        List<Rewrite> out = new ArrayList<>();
        Set<OfAnArm> seen = new HashSet<>();
        for (CoverageSites.ArmSite arm : arms) {
            if (arm.place().probe().isEmpty() || !run.lit(arm.place().probe().get())) {
                continue;
            }
            SourceConstructOrigin fork = arm.obligation().origin();
            int part = arm.obligation().part();
            for (Asked each : askedOf(fork, part, unreached)) {
                if (each instanceof Asked.Runs(Rewrite rewrite)
                        && seen.add(new OfAnArm(fork, part, rewrite.with()))) {
                    out.add(rewrite);
                }
            }
        }
        return List.copyOf(out);
    }
}
