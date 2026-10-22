package souther.bench;

import souther.compiler.meta.ModulePath;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAccount;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.BorderObligationPointAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.GenerationScope;
import souther.compiler.query.PointResolution;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * What measuring a guard over a total of independent choices costs, as the choices are added.
 *
 * <p>Each choice is a month whose pay counts toward the total only where enough days were worked, so
 * a guard over the total reads a different sum on every way the months come out. The measure owes a
 * row at each point of each of those sums, and at the days of each month along every way the months
 * before it came out — so the points owed double with each month, and a report that looked for a row
 * at every one of them is twice the work before anything is wrong with how it looks.
 *
 * <p><b>So the figure to read is the time per point, and not the time.</b> The total is what a
 * person waits for, and it grows with the points whatever the search does; what the search does is
 * what one point costs, and a search that went back over what an earlier point already worked out
 * shows there as a cost per point that grows with the months. The count of points is beside it for
 * that, and is read off the measurement rather than worked out here from the number of months: a
 * reading that started owing fewer points would otherwise come out as a faster search.
 *
 * <p><b>And what the points came to.</b> How many of them a row was composed at, how many different
 * rows that took, and how many times the border search composed one, are each read off the answers
 * the timed round produced. A row per point is what the measure promises, so rows that stop keeping
 * pace with the points say the search stopped answering, and searches that outrun the points say a
 * point was looked for more than once.
 *
 * <p><b>Set up outside the clock and measured in a store of its own.</b> Every answer the report
 * reads is kept once asked, so each round compiles afresh, says the full report is wanted, answers
 * every question a compile asks and builds the classes the search runs its rows against — and only
 * then starts the clock on the report, which is where the border search is asked for.
 */
final class SummedChoices {

    private SummedChoices() {}

    /** One month more each step, which is one doubling of the points owed. Stops short of the size
     *  a figure of this compiler's stops the reading at, where the time is the figure's and not the
     *  search's. */
    static final int[] MONTHS = {1, 2, 3, 4, 5, 6};

    /** Rounds a size is warmed for, and rounds it is the median of. Few, because one round at the
     *  largest size is many compiles' worth; three all the same, so there is a median. */
    private static final int WARMUP = 1;
    private static final int MEASURED = 3;

    static void measure(Report report) {
        for (int months : MONTHS) {
            Measured measured = time(months, WARMUP, MEASURED);
            Reached reached = measured.reached();
            report.line("SUMMED months=%d %9.1f ms  points %4d  composed %4d  distinct %4d"
                            + "  searches %5d  (%6.3f ms/point)",
                    months, measured.timing().medianMillis(), reached.points(),
                    reached.composed(), reached.distinct(), reached.searches(),
                    measured.timing().medianMillis() / Math.max(1, reached.points()));
        }
    }

    /**
     * What one measured round's report came to.
     *
     * @param points   the points of borders the module owes a row at
     * @param composed the points a row was composed at
     * @param distinct the different rows among those composed, counted by what they write
     * @param searches the times the border search composed at a point, over every reading of it
     */
    record Reached(int points, int composed, int distinct, int searches) {}

    /** The figure, and what the last of the rounds it was taken over came to. */
    record Measured(Timing timing, Reached reached) {}

    /**
     * The one way a size is run, so that what is held to arriving is what is timed.
     *
     * <p>Read off the last measured round and after its clock stopped: every round is the same
     * source in a store of its own, so one of them says what all of them did, and counting inside
     * the clock would charge the figure for the counting.
     */
    static Measured time(int months, int warmup, int measured) {
        List<Long> micros = new ArrayList<>();
        Reached reached = null;
        for (int round = 0; round < warmup + measured; round++) {
            Compilation compilation = Compilation.ofSources(List.of(source(months)),
                    ModulePath.EMPTY);
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            compilation.classes();

            long start = System.nanoTime();
            AdequacyReport.of(compilation);
            long spent = (System.nanoTime() - start) / 1000;

            if (round >= warmup) {
                micros.add(spent);
                reached = cameTo(compilation);
            }
        }
        return new Measured(new Timing(List.copyOf(micros)), reached);
    }

    private static Reached cameTo(Compilation compilation) {
        BorderAccount account = Adequacy.accountFor(compilation.db(), MODULE,
                new GenerationScope.Module());
        int composed = 0;
        int searches = 0;
        Set<List<FixtureTemplate>> written = new HashSet<>();
        for (BorderAccount.Answer answer : account.resolved().values()) {
            if (answer.resolution() instanceof PointResolution.Generated generated) {
                composed++;
                written.add(generated.row().inputs());
            }
            BorderObligationPointAssessment point = answer.point();
            for (BorderAssessment reading : point.readings()) {
                searches += point.owedAt(reading).searches().each().size();
            }
        }
        return new Reached(account.resolved().size(), composed, written.size(), searches);
    }

    private static final String MODULE = "summed.months";

    /**
     * A guard over the pay of {@code months} months, each counted where its days reach a threshold,
     * and one row that meets it.
     */
    static String source(int months) {
        StringBuilder fields = new StringBuilder();
        StringBuilder total = new StringBuilder();
        StringBuilder example = new StringBuilder();
        for (int i = 1; i <= months; i++) {
            String beside = i == 1 ? "" : ", ";
            fields.append(beside).append("m%d: Month".formatted(i));
            total.append(i == 1 ? "" : "\n        + ")
                    .append("(if y.m%d.days >= 17 then y.m%d.pay else 0)".formatted(i, i));
            example.append(beside).append("m%d = Month { pay = 1000, days = 20 }".formatted(i));
        }
        return """
                module %s

                data Month = { pay: Int, days: Int }
                data Year = { %s }
                data Ok
                data No

                behavior f : (y: Year) -> Ok | No

                let f (y) = {
                    guard %s >= 900 else No
                    Ok
                }

                example f
                    | (Year { %s }) -> Ok
                """.formatted(MODULE, fields, total, example);
    }
}
