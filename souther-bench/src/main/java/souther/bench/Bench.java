package souther.bench;

import java.util.ArrayList;
import java.util.List;

/**
 * The benchmarks, run from the command line: {@code java -jar souther-bench.jar [measurement...]}.
 *
 * <p>With no argument it runs all four. Naming one runs only that, which is how a change is checked
 * against the thing it was meant to move without waiting for the rest — {@code scale} in particular
 * compiles two hundred modules five times over.
 *
 * <pre>
 *   cold    one compile in a JVM that has not compiled before
 *   warm    the same compile in steady state
 *   phase   where a warm compile's time goes
 *   edit    what an edit costs a store that already holds the answers
 *   run     what the generated code costs to run, per element
 *   scale   how a whole-workspace compile grows with the number of modules
 * </pre>
 *
 * <p>Every corpus is compiled once and checked before anything is timed. A language change that
 * leaves a corpus behind makes the compile stop early, which is faster, and a benchmark that
 * reported that as an improvement would be worse than no benchmark.
 */
public final class Bench {

    private Bench() {}

    public static void main(String[] args) {
        Report report = new Report(System.out);
        List<String> wanted = args.length == 0
                ? List.of("cold", "warm", "phase", "edit", "run", "scale")
                : new ArrayList<>(List.of(args));

        List<Corpus> corpora = Corpus.all();
        // Cold is what the first compile in a process costs, so there is one of them: by the time a
        // second corpus is reached the JIT has seen the compiler. It is taken before anything else
        // for that reason, and it doubles as the compile each corpus is checked against.
        List<WholeCompile.Cold> cold = new ArrayList<>();
        for (Corpus corpus : corpora) {
            WholeCompile.Cold first = WholeCompile.cold(corpus);
            corpus.check(first.compilation());
            cold.add(first);
        }

        if (wanted.contains("cold")) {
            WholeCompile.report(report, corpora.getFirst(), cold.getFirst());
            report.blank();
        }
        if (wanted.contains("warm")) {
            for (Corpus corpus : corpora) {
                WholeCompile.warm(report, corpus);
            }
            report.blank();
        }
        if (wanted.contains("phase")) {
            for (Corpus corpus : corpora) {
                Phases.measure(report, corpus);
            }
            report.blank();
        }
        if (wanted.contains("edit")) {
            for (Corpus corpus : corpora) {
                Incremental.measure(report, corpus);
            }
            report.blank();
        }
        if (wanted.contains("run")) {
            Generated.measure(report);
            Generated.structure(report);
            report.blank();
        }
        if (wanted.contains("scale")) {
            Scale.measure(report);
        }
    }
}
