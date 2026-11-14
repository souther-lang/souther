package souther.compiler.conformance;

import souther.compiler.ACompiledModel;
import souther.compiler.check.DeclarationReadings;
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
 * times. The compilations are handed out to be read, each as a {@link Model}: the answers are kept in
 * each one's store, so a second reader finds the questions already put. A caller that would change
 * one — update its documents, give it another budget — makes its own rather than taking these.
 */
public final class RepositoryModels {

    /** The conformance corpora among them, as their analysis came out, by name and in the
     *  manifest's order. Filled while {@link #BY_CORPUS} is made, which is why it is declared
     *  first. */
    private static final Map<String, ConformanceCorpus.Analysed> ANALYSED = new LinkedHashMap<>();

    private static final SequencedMap<String, Model> BY_CORPUS = compileEverything();

    private static final List<Model> ALL = List.copyOf(BY_CORPUS.values());

    /** What each of them has worked out about where its sets stop, made when first asked. */
    private static final Map<Compilation, DeclarationReadings> KNOWN = new IdentityHashMap<>();

    private RepositoryModels() {
    }

    /** Every model this repository carries, each with everything about it answered. */
    public static List<Model> all() {
        return ALL;
    }

    /**
     * The same models by the name the manifest gives each corpus, in the manifest's order — for a
     * reader whose answer names one of them.
     */
    public static SequencedMap<String, Model> byCorpus() {
        return BY_CORPUS;
    }

    /**
     * The conformance corpora among them, each as the model {@link #all()} holds for it.
     *
     * <p>For a test whose subject is what the language declares it accepts and nothing written to be
     * worked with: each of these was compiled the way {@link ConformanceCorpus#analyse()} compiles
     * one, so the report built of it is the report that analysis writes.
     */
    public static Map<ConformanceCorpus, Model> conformance() {
        Map<ConformanceCorpus, Model> out = new LinkedHashMap<>();
        ANALYSED.values().forEach(each -> out.put(each.corpus(), BY_CORPUS.get(each.corpus().name())));
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
     * One model of the repository, and what it is written to be.
     *
     * <p>The compilation is not handed out as it is. A corpus is written to compile or to be refused
     * with the errors it declares, and a test that took the compilation and held it to one of those
     * by its own choosing would hold some of them to the wrong one. The only way to the compilation
     * is {@link #answered()}, which holds it to what the corpus declares, so no test chooses.
     */
    public static final class Model {

        private final String name;

        private final Compilation compilation;

        private final List<String> refusedWith;

        private Model(String name, Compilation compilation, List<String> refusedWith) {
            this.name = name;
            this.compilation = compilation;
            this.refusedWith = refusedWith;
        }

        /** The name the manifest gives its corpus. */
        public String name() {
            return name;
        }

        /**
         * The compilation, answered in full and held to be refused with what its corpus is written
         * to be refused with and nothing else, which is nothing for a model written to compile.
         * Already held to that where it is a conformance corpus; the same compilation every time.
         */
        public Compilation answered() {
            return ACompiledModel.refusedWith(refusedWith, compilation);
        }
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
     * <p><b>For the models {@link #all()} hands out and no others, which is why it takes one.</b>
     * What is kept here is knowledge of one revision, and a compilation is not one: the same object
     * takes another set of sources when it is updated, and what its sets are is then settled by
     * sources these answers were not worked out under. These are never updated — they are the
     * models as this repository carries them, compiled once for the JVM — so the object stands in
     * for the revision here and would not anywhere else. A compilation a test makes for itself
     * lends its own, {@code db().readings()}.
     */
    public static synchronized DeclarationReadings knownTo(Model model) {
        return KNOWN.computeIfAbsent(model.compilation, _ -> knowingWhereSetsStop());
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

    private static SequencedMap<String, Model> compileEverything() {
        SequencedMap<String, Model> out = new LinkedHashMap<>();
        for (Map.Entry<String, String> corpus : ConformanceCorpus.manifest().entrySet()) {
            if (corpus.getValue().equals(ConformanceCorpus.CONFORMANCE)) {
                // The analysing entry point, which is what says a conformance corpus was analysed:
                // it puts the adequacy questions as well as compiling.
                ConformanceCorpus.Analysed analysed = ConformanceCorpus.load(corpus.getKey()).analyse();
                ANALYSED.put(corpus.getKey(), analysed);
                out.put(corpus.getKey(), new Model(corpus.getKey(), analysed.answered(),
                        analysed.corpus().refusedWith()));
            } else {
                ConformanceCorpus loaded = ConformanceCorpus.load(corpus.getKey());
                out.put(corpus.getKey(),
                        new Model(corpus.getKey(), loaded.answered(), loaded.refusedWith()));
            }
        }
        return Collections.unmodifiableSequencedMap(out);
    }
}
