package souther.compiler.conformance;

import souther.compiler.TestDay;
import souther.compiler.check.DeclarationReadings;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.revision.RevisionKnowledge;
import souther.compiler.revision.StoreWork;
import souther.compiler.types.TypeKey;
import souther.compiler.values.StringMachineAnswers;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;

/**
 * Every model this repository carries, compiled and answered.
 *
 * <p>The population a test asks about when its subject is the language rather than one source: the
 * conformance corpora, which are what the language declares it accepts, and the models written to be
 * worked with, which reach a construct under conditions nobody wrote it for. A test that sweeps
 * positions, rules or readings is asking about all of them, and asking about a smaller set would
 * make its answer one about the fixtures it happened to name.
 *
 * <p><b>Which models those are is not said here.</b> The manifest names every corpus this repository
 * carries and each corpus's {@code sources.txt} names its files; both are read and neither is
 * restated. A membership written out here would be a second account of the same fact, and the two
 * answer separately without anything failing — a corpus added to the manifest is simply not in the
 * population, and a check over every model passes while covering fewer.
 *
 * <p><b>Built once for the JVM that asks.</b> Answering these is most of what such a test costs, and
 * a class with three questions about the population would otherwise pay for the population three
 * times. The compilations are handed out to be read: the answers are kept in each one's store, so a
 * second reader finds the questions already put. A caller that would change one — update its
 * documents, give it another budget — makes its own rather than taking these.
 */
public final class RepositoryModels {

    /** The conformance corpora among them, as their analysis came out, by name and in the
     *  manifest's order. Filled while {@link #BY_CORPUS} is made, which is why it is declared
     *  first. */
    private static final Map<String, ConformanceCorpus.Analysed> ANALYSED = new LinkedHashMap<>();

    private static final SequencedMap<String, Compilation> BY_CORPUS = compileEverything();

    private static final List<Compilation> ALL = List.copyOf(BY_CORPUS.values());

    /** What each of them has worked out about where its sets stop, made when first asked. */
    private static final Map<Compilation, DeclarationReadings> KNOWN = new IdentityHashMap<>();

    private RepositoryModels() {
    }

    /** Every model this repository carries, each with everything about it answered. */
    public static List<Compilation> all() {
        return ALL;
    }

    /**
     * The same models by the name the manifest gives each corpus, in the manifest's order — for a
     * reader whose answer names one of them.
     */
    public static SequencedMap<String, Compilation> byCorpus() {
        return BY_CORPUS;
    }

    /**
     * The conformance corpora among them, each with the compilation {@link #all()} holds for it.
     *
     * <p>For a test whose subject is what the language declares it accepts and nothing written to be
     * worked with: each of these was compiled the way {@link ConformanceCorpus#analyse()} compiles
     * one, so the report built of it is the report that analysis writes.
     */
    public static Map<ConformanceCorpus, Compilation> conformance() {
        Map<ConformanceCorpus, Compilation> out = new LinkedHashMap<>();
        ANALYSED.values().forEach(each -> out.put(each.corpus(), each.compilation()));
        return Collections.unmodifiableMap(out);
    }

    /**
     * A conformance corpus as {@link #all()} holds it: the same compilation, with what its analysis
     * said and the report it measured.
     *
     * <p>For a test whose subject is the conformance corpora and not every model. It reads the
     * analysis the population already holds rather than making one of its own, which would be the
     * same answers worked out again.
     */
    public static ConformanceCorpus.Analysed analysed(ConformanceCorpus corpus) {
        ConformanceCorpus.Analysed held = ANALYSED.get(corpus.name());
        if (held == null) {
            throw new IllegalArgumentException(corpus + " is not a conformance corpus the manifest"
                    + " names");
        }
        return held;
    }

    /**
     * What one of these models already knows, to be handed to every reading made of it.
     *
     * <p>Where a set's strings stop is settled by the set and by an allowance minted for that set,
     * so it is one answer for the model and not one per reading ({@link RevisionKnowledge}). A test
     * that reads a declaration once has nothing to gain from this; one that reads every declaration
     * of every model, or one declaration under every settling of its coordinates, meets the same
     * sets again at each of them and walks each of them again without it.
     *
     * <p><b>This and nothing else.</b> What a reading of a declaration came to is what such a test
     * is usually about, so no reading is lent here — a lender that handed one would be answering
     * the question instead of sharing the work under it.
     *
     * <p><b>For the compilations {@link #all()} hands out and no others.</b> What is kept here is
     * knowledge of one revision, and a compilation is not one: the same object takes another set of
     * sources when it is updated, and what its sets are is then settled by sources these answers
     * were not worked out under. These are never updated — they are the models as this repository
     * carries them, compiled once for the JVM — so the object stands in for the revision here and
     * would not anywhere else.
     */
    public static synchronized DeclarationReadings knownTo(Compilation compilation) {
        return KNOWN.computeIfAbsent(compilation, _ -> knowingWhereSetsStop());
    }

    private static DeclarationReadings knowingWhereSetsStop() {
        // One revision for as long as the JVM lives, for the reason given above.
        RevisionKnowledge known = RevisionKnowledge.keptFor(() -> 0L, StoreWork.UNWATCHED);
        return new DeclarationReadings() {

            @Override
            public StringMachineAnswers of(TypeKey declaration) {
                return StringMachineAnswers.unborrowed(known);
            }

            @Override
            public RevisionKnowledge revision() {
                return known;
            }
        };
    }

    private static SequencedMap<String, Compilation> compileEverything() {
        SequencedMap<String, Compilation> out = new LinkedHashMap<>();
        for (Map.Entry<String, String> corpus : ConformanceCorpus.manifest().entrySet()) {
            if (corpus.getValue().equals(ConformanceCorpus.CONFORMANCE)) {
                // The analysing entry point, which is what says a conformance corpus was analysed:
                // it puts the adequacy questions as well as compiling.
                ConformanceCorpus.Analysed analysed = ConformanceCorpus.load(corpus.getKey()).analyse();
                ANALYSED.put(corpus.getKey(), analysed);
                out.put(corpus.getKey(), analysed.compilation());
            } else {
                Compilation compilation = Compilation.ofSources(
                        ConformanceCorpus.sourcesOf(corpus.getKey()), ModulePath.EMPTY)
                        .writtenOn(TestDay.DATE);
                compilation.answerEverything();
                out.put(corpus.getKey(), compilation);
            }
        }
        return Collections.unmodifiableSequencedMap(out);
    }
}
