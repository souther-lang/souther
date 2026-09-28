package souther.bench;

import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Offering;
import souther.compiler.query.OfferingRequest;

import java.util.ArrayList;
import java.util.List;

/**
 * What looking for the rows a model does not cover costs, asked of a module at a time.
 *
 * <p>What a request asks for is two searches, and the figure is what answering it costs: the
 * combinations a behavior's own rows have not covered, and a row at each point of a border — the
 * second asking where the positions have to stand, narrowing a region as each is chosen, walking
 * what is left, and stopping at figures of this compiler's where a walk runs long. It is the second
 * that nothing a compile asks for reaches — a build asks for classes, and the rows are asked for by
 * a person — so the figures those walks are held to could be changed either way with every number
 * this repository takes staying where it was.
 *
 * <p><b>Not a phase.</b> {@link Phases} takes one warm compile apart into lines that add up to it,
 * and this is not part of a compile: it is an operation somebody asks for afterwards, and over a
 * model whose rules bound its numbers it costs many times what compiling that model costs. Put in
 * that list it would leave every other line at nothing and a total that is no longer a compile's.
 *
 * <p><b>What the store has asked for, and what it has not.</b> The compilation says up front that
 * it is measuring everything a report says ({@link Adequacy.Asked#fullReport()}), which is what the
 * command offering the rows says, and what a measurement of the offering has to state rather than
 * take from a default. What it must not do is ask anything the offering is about before the clock
 * starts: the searches are keyed, so a store that had asked for the warnings — or for the written
 * tables, whose rows are run against instrumented classes at this level — would have paid for the
 * very walks this is the time of, and the figure would be what is left after somebody else paid.
 * So the set-up is the structural reports and the classes, and no more.
 *
 * <p>The classes rather than nothing, because the search puts values through this module's decoders
 * to find out what a row would settle. Left to be built inside the clock, the figure would hold what
 * turning Souther into JVM classes costs beside what looking for a value costs, and a change to
 * either would move it.
 *
 * <p><b>A store per sample.</b> An answer is kept once, so asking a second time measures a lookup.
 * Every round therefore builds its own store and pays its own set-up outside the figure, which is
 * what makes the rounds comparable rather than a first round and a series of reads.
 */
final class RowOffering {

    private RowOffering() {}

    /**
     * Rounds the figure is warmed for, and rounds it is taken over.
     *
     * <p>Fewer than a compile is measured over, because one round here is the cost of many compiles
     * and the JIT has already seen the compiler by the time this runs. Three all the same: one round
     * is a number with a collection or an interrupted machine in it and nothing to say so, and three
     * have a median.
     */
    private static final int WARMUP = 1;
    private static final int MEASURED = 3;

    /** The median and the floor, and no quantile between them: a ninetieth taken over as few rounds
     *  as these is the largest of them under a name that says it is not. */
    static void measure(Report report, Corpus corpus) {
        Timing timing = timeOfferings(corpus, WARMUP, MEASURED).timing();
        report.line("OFFER %-14s median %8.1f ms  min %8.1f ms", corpus.name(),
                timing.medianMillis(), timing.minMillis());
    }

    /**
     * The figure, and what the offerings it was taken over came to.
     *
     * @param timing what asking for the rows cost
     * @param reached what the searches behind those answers produced
     */
    record Offered(Timing timing, Reached reached) {}

    /**
     * What the offerings a figure was taken over answered with.
     *
     * <p>Beside the figure for the reason every other measurement here carries a reading: a number
     * for a walk nothing arrives at is a number, and nothing about it says which of the two it is.
     * This is the defect this measurement exists because of, so the measurement answers for itself.
     *
     * <p><b>A field per search, each read off that search's own answer.</b> A request is answered by
     * two of them and the answer keeps them apart, because filling a combination and writing a row
     * at an edge are different requests asked with different flags. So what a border search reached
     * is read from the border search: counted from the combinations, the figure would stand while
     * the borders went dark, which is the state this measurement exists to catch and would then be
     * the state it was in.
     *
     * <p>Answered rather than unresolved. A search says what it has to say in rows, in what it could
     * not resolve, and in what stopped it; a border search that composed a row for every point has
     * nothing unresolved and ran all the same, so what is asked of it is whether it came back with
     * anything ({@link souther.compiler.partition.Generator.GenerationResult#isEmpty()}).
     *
     * <p>Added up over the rounds the figure was taken over, and over the modules of each. What is
     * asked of it is whether the walks happened at all, which a total answers; what one round or one
     * module came to is a question about that round or that module and is not one this is here for.
     *
     * @param offers what the offerings put in front of a reader to complete, from both searches,
     *               naming neither
     * @param bordersAnswered behaviors whose border search came back with something to say
     */
    record Reached(int offers, int bordersAnswered) {

        Reached and(Reached other) {
            return new Reached(offers + other.offers(),
                    bordersAnswered + other.bordersAnswered());
        }
    }

    /**
     * The one way this is run, so that what is held to arriving is what is timed.
     *
     * <p>The reading is taken out of the answers the timed rounds produced, and taken after the
     * clock stops: counting inside it would charge the figure for reading what it had just asked
     * for.
     */
    static Offered timeOfferings(Corpus corpus, int warmup, int measured) {
        List<Long> micros = new ArrayList<>();
        Reached reached = new Reached(0, 0);
        for (int round = 0; round < warmup + measured; round++) {
            Compilation compilation = Compilation.ofSources(corpus.sources(), ModulePath.EMPTY);
            // Said before anything is asked, because the answers are kept: a level set later would
            // leave the questions already answered measured at one level and the rest at another.
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.structuralReports();
            compilation.classes();

            long start = System.nanoTime();
            List<Offering> answers = offerings(compilation);
            long spent = (System.nanoTime() - start) / 1000;

            if (round >= warmup) {
                micros.add(spent);
                reached = reached.and(cameTo(answers));
            }
        }
        return new Offered(new Timing(List.copyOf(micros)), reached);
    }

    /** What a person asking for the rows of every module asks, which is one request per module. */
    private static List<Offering> offerings(Compilation compilation) {
        List<Offering> answers = new ArrayList<>();
        for (String module : compilation.modules()) {
            Offering one = Adequacy.offeredFor(compilation.db(),
                    OfferingRequest.overTheModule(module));
            if (one != null) {
                answers.add(one);
            }
        }
        return answers;
    }

    private static Reached cameTo(List<Offering> answers) {
        int offers = 0;
        int bordersAnswered = 0;
        for (Offering offering : answers) {
            offers += offering.count();
            for (Adequacy.Filling filling : offering.searched().values()) {
                if (!filling.boundaries().isEmpty()) {
                    bordersAnswered++;
                }
            }
        }
        return new Reached(offers, bordersAnswered);
    }
}
