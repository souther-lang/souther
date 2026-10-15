package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.types.ValueName;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What proving the operations the library writes against their bodies came to when this compiler
 * was built, shipped with it and read in place of proving them again.
 *
 * <p>The same answer as proving them here, by how it is made: the build proves them with the very
 * classes and library it ships and writes down what each proof came to ({@link #main}), and nothing
 * else writes it. Read rather than proved because a proof comes out the same every time it is made,
 * and making them all is most of what a compilation's start would cost. A test proves them here and
 * holds the facts read off this to the facts proved.
 *
 * <p>Where something stated was left unproved, this is not read: why it was not proved is what a
 * reader of an open statement is told, and proving it again is where the reason comes from.
 */
public final class LibraryProofsAsBuilt {

    /** Where the record stands among the classes. */
    static final String RESOURCE = "souther/compiler/check/library-proofs.txt";

    private static final String LAW = "law";
    private static final String CLOSED = "closed";
    private static final String OPEN = "open";
    private static final String NOTHING = "nothing";
    private static final String HOLDS = "holds";
    private static final String DOES_NOT_HOLD = "does-not-hold";

    /** What each proof came to, by what it was a proof of. */
    private final Map<String, String> outcomes;

    private LibraryProofsAsBuilt(Map<String, String> outcomes) {
        this.outcomes = Map.copyOf(outcomes);
    }

    /**
     * How what the shipped library's written operations state is proved: read off the record
     * built with them, where there is one and it holds everything stated proved, and proved here
     * otherwise.
     */
    static LibraryProofs.Source shippedOrProving() {
        Map<String, String> read = read();
        if (read == null || read.containsValue(OPEN) || read.containsValue(DOES_NOT_HOLD)) {
            return LibraryProofs.PROVING;
        }
        LibraryProofsAsBuilt record = new LibraryProofsAsBuilt(read);
        return (_, _, _, stated, awaiting) -> record.over(stated, awaiting);
    }

    /** Proves the library here and writes what each proof came to at {@code args[0]}. */
    public static void main(String[] args) throws IOException {
        Map<String, String> outcomes = new LinkedHashMap<>();
        OperationFactBinder.bindAll(DefaultStdlib.get(), recording(outcomes));
        Path to = Path.of(args[0]);
        Files.createDirectories(to.getParent());
        List<String> lines = new ArrayList<>(outcomes.size());
        outcomes.forEach((what, cameTo) -> lines.add(what + "\t" + cameTo));
        Files.write(to, lines, StandardCharsets.UTF_8);
    }

    /** The proofs read off this record, of what {@code stated} and {@code awaiting} say. */
    private LibraryProofs over(Map<ValueName.Stdlib.Operation,
                                       Map<OperationLaw.Observed, ProvingTheLibrary.Stated>> stated,
                               List<BoundOperationFact> awaiting) {
        Map<BoundOperationFact, String> named = named(awaiting);
        return new LibraryProofs() {

            @Override
            public BoundOperationFacts.Settled settle(ValueName.Stdlib.Operation operation,
                                                      OperationLaw.Observed observed) {
                ProvingTheLibrary.Stated what =
                        stated.getOrDefault(operation, Map.of()).get(observed);
                String cameTo = outcomes.get(settling(operation, observed));
                return switch (cameTo) {
                    case LAW -> new BoundOperationFacts.Settled.ByALaw(what.law(),
                            new BoundOperationFacts.Grounds.ProvedWhenBuilt());
                    case CLOSED -> new BoundOperationFacts.Settled.Unsaid(what.closedAs());
                    case NOTHING -> null;
                    case null, default -> throw ofAnotherBuild(settling(operation, observed));
                };
            }

            @Override
            public boolean proves(BoundOperationFact fact) {
                String cameTo = outcomes.get(named.get(fact));
                if (!HOLDS.equals(cameTo)) {
                    throw ofAnotherBuild(named.get(fact));
                }
                return true;
            }
        };
    }

    /** The proving here, with what each proof came to written into {@code outcomes}. */
    private static LibraryProofs.Source recording(Map<String, String> outcomes) {
        return (stdlib, facts, settled, stated, awaiting) -> {
            LibraryProofs proving =
                    LibraryProofs.PROVING.over(stdlib, facts, settled, stated, awaiting);
            Map<BoundOperationFact, String> named = named(awaiting);
            return new LibraryProofs() {

                @Override
                public BoundOperationFacts.Settled settle(ValueName.Stdlib.Operation operation,
                                                          OperationLaw.Observed observed) {
                    BoundOperationFacts.Settled settling = proving.settle(operation, observed);
                    outcomes.put(settling(operation, observed), switch (settling) {
                        case null -> NOTHING;
                        case BoundOperationFacts.Settled.ByALaw _ -> LAW;
                        case BoundOperationFacts.Settled.Unsaid _ -> CLOSED;
                        case BoundOperationFacts.Settled.Open _ -> OPEN;
                    });
                    return settling;
                }

                @Override
                public boolean proves(BoundOperationFact fact) {
                    boolean holds = proving.proves(fact);
                    outcomes.put(named.get(fact), holds ? HOLDS : DOES_NOT_HOLD);
                    return holds;
                }
            };
        };
    }

    /** What settling {@code observed} of {@code operation} is a proof of, as the record says it. */
    private static String settling(ValueName.Stdlib.Operation operation,
                                   OperationLaw.Observed observed) {
        return "settles\t" + operation + "\t" + observed;
    }

    /** Each fact of {@code awaiting} as the record says it: its place among them, its operation
     *  and its kind, so a record of another set of facts is not read for this one. */
    private static Map<BoundOperationFact, String> named(List<BoundOperationFact> awaiting) {
        Map<BoundOperationFact, String> out = new IdentityHashMap<>();
        for (int at = 0; at < awaiting.size(); at++) {
            BoundOperationFact fact = awaiting.get(at);
            out.put(fact, "states\t" + at + "\t" + fact.operation().operation() + "\t"
                    + fact.getClass().getSimpleName());
        }
        return out;
    }

    private static IllegalStateException ofAnotherBuild(String what) {
        return new IllegalStateException("the proofs shipped with this compiler say nothing of "
                + what + ": they were written by another build of it");
    }

    /** The record shipped with these classes, or null where there is none. */
    private static Map<String, String> read() {
        try (InputStream in = LibraryProofsAsBuilt.class.getClassLoader()
                .getResourceAsStream(RESOURCE)) {
            if (in == null) {
                return null;
            }
            Map<String, String> out = new LinkedHashMap<>();
            BufferedReader lines = new BufferedReader(
                    new InputStreamReader(in, StandardCharsets.UTF_8));
            for (String line = lines.readLine(); line != null; line = lines.readLine()) {
                int last = line.lastIndexOf('\t');
                out.put(line.substring(0, last), line.substring(last + 1));
            }
            return out;
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
