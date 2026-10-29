package souther.compiler.coverage;

import souther.compiler.types.SourceConstructOrigin;

import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.SequencedMap;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * Which rewrites each numbered walk can be run as ({@link WalkRewrite}).
 *
 * <p>What a row is asked to notice of a walk. The classes that record where a run goes carry, at
 * every walk, a switch nothing turns on unless a run asks for it ({@link Intervention}); this says,
 * of every numbered walk, whether the switch is there and which rewrites are the walk under another
 * spelling.
 *
 * <p>Keyed by the walk's site, as {@link ArmReplacements} is keyed by an arm's. Several sites are
 * one walk where a helper holding it is spliced into several bodies, and the walk an author wrote is
 * {@link AtWalk#walk}: a rewrite is of that walk, so it stands at every site of it at once, as an
 * edit of the source would.
 *
 * <p>A function of the bodies alone, less the walks a method could not hold the switch in. The
 * emitter and whatever reads a run are handed the same one.
 *
 * @param bySite every numbered walk, by its site, in the order of the sites
 */
public record WalkRewrites(SequencedMap<Integer, AtWalk> bySite) {

    public WalkRewrites {
        bySite = Collections.unmodifiableSequencedMap(new TreeMap<>(bySite));
    }

    /** No walk can be rewritten: what a build that records nothing carries. */
    public static final WalkRewrites NONE = new WalkRewrites(new TreeMap<>());

    /**
     * One numbered walk.
     *
     * @param walk           the walk the author wrote, which every site of it shares
     * @param at             where entering it is recorded
     * @param theSame        the rewrites the source shows to be the walk under another spelling
     *                       here: a list written with no more than one element is walked no further
     *                       than its first, and a step that never reads what it carries is handed
     *                       the seed to no effect
     * @param overAFixedList whether the list walked reads nothing a run is handed, so that it is
     *                       one list on every run, and a run seen walking it no further than its
     *                       first element shows every run does
     * @param notCarried     why the classes do not carry the switch here, where they do not
     */
    public record AtWalk(SourceConstructOrigin walk, WalkProbe at, Set<WalkRewrite> theSame,
                         boolean overAFixedList,
                         Optional<ArmReplacements.Sibling.Why> notCarried) {

        public AtWalk {
            Objects.requireNonNull(walk, "a walk is some walk an author wrote");
            Objects.requireNonNull(at, "a walk is entered somewhere");
            theSame = theSame.isEmpty() ? Set.of() : Set.copyOf(EnumSet.copyOf(theSame));
            Objects.requireNonNull(notCarried, "the switch is carried or it is not");
        }

        /**
         * Whether {@code how} is the walk under another spelling here: shown by the source, or by
         * a run that walked a list the same on every run no further than its first element
         * ({@code walkedNoFurther}).
         */
        boolean leaves(WalkRewrite how, WalkedNoFurther walkedNoFurther) {
            return theSame.contains(how) || (overAFixedList && walkedNoFurther.at(at));
        }
    }

    /**
     * These rewrites with nothing carried at {@code sites}: what the classes hold where the emitter
     * wrote the walks there without their switch, because the method they are in would otherwise
     * be more than the JVM holds.
     */
    public WalkRewrites carryingNothingAt(Set<Integer> sites) {
        SequencedMap<Integer, AtWalk> out = new TreeMap<>();
        bySite.forEach((site, at) -> out.put(site, sites.contains(site)
                ? new AtWalk(at.walk(), at.at(), at.theSame(), at.overAFixedList(),
                        Optional.of(new ArmReplacements.Sibling.Why.PastWhatAMethodHolds()))
                : at));
        return new WalkRewrites(out);
    }

    /** Every site of {@code walk}, in the order of the sites. */
    public List<AtWalk> ofWalk(SourceConstructOrigin walk) {
        return bySite.values().stream().filter(at -> at.walk().equals(walk)).toList();
    }

    /**
     * The sites a run asks for to run {@code walk} as {@code how}: every site of the walk whose
     * classes carry the switch, each mapped to {@code how}.
     */
    public SequencedMap<Integer, WalkRewrite> replacing(SourceConstructOrigin walk,
                                                        WalkRewrite how) {
        SequencedMap<Integer, WalkRewrite> sites = new LinkedHashMap<>();
        bySite.forEach((site, at) -> {
            if (at.walk().equals(walk) && at.notCarried().isEmpty()) {
                sites.put(site, how);
            }
        });
        return sites;
    }

    /**
     * One rewrite a run can be asked for: {@code walk} run as {@code how}, at {@code replacing}'s
     * sites ({@link #replacing}).
     */
    public record Rewrite(SourceConstructOrigin walk, WalkRewrite how,
                          SequencedMap<Integer, WalkRewrite> replacing) implements RunRewrite {

        public Rewrite {
            Objects.requireNonNull(walk, "a walk is some walk an author wrote");
            Objects.requireNonNull(how, "a walk is rewritten some way");
            replacing = Collections.unmodifiableSequencedMap(new TreeMap<>(replacing));
        }

        @Override
        public Rewriting asked() {
            return Rewriting.ofWalks(replacing);
        }
    }

    /** One rewrite of one walk, apart from where it is run. */
    private record OfAWalk(SourceConstructOrigin walk, WalkRewrite how) {}

    /**
     * Every rewrite a run that entered the walks at {@code sites} can be run as: each rewrite of
     * each walk whose classes carry the switch at one of those sites, once per walk and rewrite
     * however many of its sites the run entered, in the order of the sites and then of the
     * rewrites.
     *
     * <p>What a recording is run again under, which is more than a row is asked
     * ({@link #askedOfARun}): a rewrite that is the walk under another spelling is run here too.
     */
    public List<Rewrite> through(Set<Integer> sites) {
        List<Rewrite> out = new ArrayList<>();
        Set<OfAWalk> seen = new HashSet<>();
        for (int site : new TreeSet<>(sites)) {
            AtWalk at = bySite.get(site);
            if (at == null || at.notCarried().isPresent()) {
                continue;
            }
            for (WalkRewrite how : WalkRewrite.values()) {
                if (seen.add(new OfAWalk(at.walk(), how))) {
                    out.add(new Rewrite(at.walk(), how, replacing(at.walk(), how)));
                }
            }
        }
        return List.copyOf(out);
    }

    /** What one rewrite of a walk comes to as a question a row entering the walk is asked. */
    public sealed interface Asked {

        /** The way the walk is rewritten. */
        WalkRewrite how();

        /** It can be run, at every site of the walk, as {@code rewrite}. */
        record Runs(Rewrite rewrite) implements Asked {

            @Override
            public WalkRewrite how() {
                return rewrite.how();
            }
        }

        /** Some site of the walk does not carry the switch, so no run is the rewrite: a run at the
         *  sites that do is a program the author could not write. */
        record NotRun(WalkRewrite how, ArmReplacements.Sibling.Why why) implements Asked {}
    }

    /**
     * Every rewrite of {@code walk} that is another program, and what each comes to as a question:
     * in the order of the rewrites.
     *
     * <p>A rewrite stands at every site of the walk at once, so it is the walk under another
     * spelling only where it is at each of them. And it can be run only where every site carries
     * the switch.
     *
     * <p>{@code walkedNoFurther} is the sites some run that answered entered and no such run took
     * a second element of, as the rows written were seen: at a site whose list is one list on
     * every run, that is a proof the list holds one element at most.
     *
     * <p>The one answer to which rewrites a row entering the walk is asked, whoever asks: the
     * measure of the rows written and the composer choosing a row to offer put the same questions.
     */
    public List<Asked> askedOf(SourceConstructOrigin walk, WalkedNoFurther walkedNoFurther) {
        List<AtWalk> sites = ofWalk(walk);
        List<Asked> out = new ArrayList<>();
        for (WalkRewrite how : WalkRewrite.values()) {
            if (sites.stream().allMatch(at -> at.leaves(how, walkedNoFurther))) {
                continue;
            }
            Optional<ArmReplacements.Sibling.Why> left = sites.stream()
                    .map(AtWalk::notCarried).flatMap(Optional::stream).findFirst();
            out.add(left.isPresent() ? new Asked.NotRun(how, left.get())
                    : new Asked.Runs(new Rewrite(walk, how, replacing(walk, how))));
        }
        return List.copyOf(out);
    }

    /**
     * The rewrites a row whose run is {@code run} is asked and can be run as: those of each walk of
     * {@code walks} the run entered ({@link #askedOf}), once per walk and rewrite, in the order of
     * {@code walks} and then of the rewrites.
     */
    public List<Rewrite> askedOfARun(List<CoverageSites.WalkSite> walks, AlignedObservation run,
                                     WalkedNoFurther walkedNoFurther) {
        List<Rewrite> out = new ArrayList<>();
        Set<OfAWalk> seen = new HashSet<>();
        for (CoverageSites.WalkSite walk : walks) {
            if (!run.entered(walk.index())) {
                continue;
            }
            for (Asked each : askedOf(walk.walk(), walkedNoFurther)) {
                if (each instanceof Asked.Runs(Rewrite rewrite)
                        && seen.add(new OfAWalk(walk.walk(), rewrite.how()))) {
                    out.add(rewrite);
                }
            }
        }
        return List.copyOf(out);
    }
}
