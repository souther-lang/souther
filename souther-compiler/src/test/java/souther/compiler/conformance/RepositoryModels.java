package souther.compiler.conformance;

import souther.compiler.check.DeclarationReadings;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.types.TypeKey;
import souther.compiler.values.KnownExtents;
import souther.compiler.values.StringMachineAnswers;
import souther.compiler.values.TextExtent;
import souther.compiler.values.ValueSet;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

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

    private static final List<Compilation> ALL = compileEverything();

    /** What each of them has worked out about where its sets stop, made when first asked. */
    private static final Map<Compilation, DeclarationReadings> KNOWN = new IdentityHashMap<>();

    private RepositoryModels() {
    }

    /** Every model this repository carries, each with everything about it answered. */
    public static List<Compilation> all() {
        return ALL;
    }

    /**
     * What one of these models already knows, to be handed to every reading made of it.
     *
     * <p>Where a set's strings stop is settled by the set and by an allowance minted for that set,
     * so it is one answer for the model and not one per reading ({@link KnownExtents}). A test that
     * reads a declaration once has nothing to gain from this; one that reads every declaration of
     * every model, or one declaration under every settling of its coordinates, meets the same sets
     * again at each of them and walks each of them again without it.
     *
     * <p><b>This and nothing else.</b> What a reading of a declaration came to is what such a test
     * is usually about, so no reading is lent here — a lender that handed one would be answering
     * the question instead of sharing the work under it.
     */
    public static synchronized DeclarationReadings knownTo(Compilation compilation) {
        return KNOWN.computeIfAbsent(compilation, _ -> knowingWhereSetsStop());
    }

    private static DeclarationReadings knowingWhereSetsStop() {
        Map<ValueSet, TextExtent> stops = new HashMap<>();
        KnownExtents extents = new KnownExtents() {

            @Override
            public TextExtent of(ValueSet set) {
                return stops.get(set);
            }

            @Override
            public void remember(ValueSet set, TextExtent extent) {
                stops.put(set, extent);
            }
        };
        return new DeclarationReadings() {

            @Override
            public StringMachineAnswers of(TypeKey declaration) {
                return StringMachineAnswers.unborrowed(extents);
            }

            @Override
            public KnownExtents extents() {
                return extents;
            }
        };
    }

    private static List<Compilation> compileEverything() {
        List<Compilation> out = new ArrayList<>();
        for (Map.Entry<String, String> corpus : ConformanceCorpus.manifest().entrySet()) {
            if (corpus.getValue().equals(ConformanceCorpus.CONFORMANCE)) {
                // The analysing entry point, which is what says a conformance corpus was analysed:
                // it puts the adequacy questions as well as compiling.
                out.add(ConformanceCorpus.load(corpus.getKey()).analyse().compilation());
            } else {
                Compilation compilation = Compilation.ofSources(
                        ConformanceCorpus.sourcesOf(corpus.getKey()), ModulePath.EMPTY);
                compilation.answerEverything();
                out.add(compilation);
            }
        }
        return List.copyOf(out);
    }
}
