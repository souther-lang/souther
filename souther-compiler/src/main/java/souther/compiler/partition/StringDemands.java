package souther.compiler.partition;

import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.core.Core;
import souther.compiler.coverage.RunBodies;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

/**
 * What the bodies of a run ask of the pieces of a string they part: where they part it, and the
 * newtypes they go on to attempt a construction of.
 *
 * <p>Read off the bodies and off what the library states of the operations that part a string
 * ({@link BoundOperationFacts#piecesOf}), so no operation is named here. What strings a newtype
 * accepts is not read here either: that is what the values that stand for its type are, asked of
 * the input ({@link MeasuredInput#representativesHolding}), so a rule about a string is meant one
 * way everywhere.
 *
 * <p>The candidates this offers are a place to look and nothing more. That a string parted at a
 * separator has each piece among the values a newtype stands for does not make it a value the
 * rewrite answers differently on: whether it does is what running the body and the rewrite on it
 * says, as it is for every candidate a search is asked about.
 */
public final class StringDemands {

    /** The bodies ask nothing of the pieces of a string. */
    public static final StringDemands NONE = new StringDemands(List.of(), List.of());

    private final List<Integer> separators;
    private final List<Type> attempted;

    private StringDemands(List<Integer> separators, List<Type> attempted) {
        this.separators = List.copyOf(separators);
        this.attempted = List.copyOf(attempted);
    }

    /** What the bodies {@code run} goes through ask of the pieces of a string. */
    public static StringDemands of(RunBodies run, RuleReadingSource source) {
        Set<Integer> separators = new LinkedHashSet<>();
        Set<Type> attempted = new LinkedHashSet<>();
        if (run.entry() != null) {
            collect(run.entry(), source, separators, attempted);
        }
        run.analysis().ifPresent(body -> collect(body.core(), source, separators, attempted));
        for (Core method : run.methods()) {
            collect(method, source, separators, attempted);
        }
        return separators.isEmpty() || attempted.isEmpty() ? NONE
                : new StringDemands(new ArrayList<>(separators), new ArrayList<>(attempted));
    }

    private static void collect(Core e, RuleReadingSource source, Set<Integer> separators,
                                Set<Type> attempted) {
        Core node = Core.withoutStanding(e);
        if (node instanceof Core.PreservedCall call
                && call.declared().operation() instanceof ValueName.Stdlib operation) {
            separatorOf(operation, call.args(), separators);
        } else if (node instanceof Core.Call call && call.fn() instanceof Core.Reached reached
                && reached.denotes() instanceof ValueName.Stdlib operation) {
            separatorOf(operation, call.args(), separators);
        }
        if (node instanceof Core.IfConstructed made
                && source.newtypes().of(made.construct().typeName().key())) {
            attempted.add(made.construct().type());
        }
        Core.forEachChild(node, child -> collect(child, source, separators, attempted));
    }

    /** The code point {@code operation} parts a string at, where it is called with a separator
     *  written out as one code point. */
    private static void separatorOf(ValueName.Stdlib operation, List<Core> args,
                                    Set<Integer> separators) {
        BoundOperationFacts.Pieces parted = DefaultBoundOperationFacts.get().piecesOf(operation);
        if (parted == null || parted.separator().isEmpty()
                || !(Core.withoutStanding(args.get(parted.separator().get().position()))
                        instanceof Core.Str written)) {
            return;
        }
        String text = written.value();
        if (text.codePointCount(0, text.length()) == 1
                && !(text.length() == 1 && Character.isSurrogate(text.charAt(0)))) {
            separators.add(text.codePointAt(0));
        }
    }

    /** The newtypes the bodies attempt a construction of. */
    List<Type> attempted() {
        return attempted;
    }

    /**
     * The strings {@code seen} becomes where its pieces, parted at a separator the bodies part a
     * string at, are put among the strings {@code standingFor} gives for a newtype they go on to
     * attempt a construction of: each piece in turn, and all of them together. A string that holds
     * no separator is not parted, and the string itself is no candidate.
     */
    List<String> besides(String seen, Function<Type, List<String>> standingFor) {
        List<String> witnesses = new ArrayList<>();
        for (Type type : attempted) {
            for (String each : standingFor.apply(type)) {
                if (!witnesses.contains(each)) {
                    witnesses.add(each);
                }
            }
        }
        List<String> out = new ArrayList<>();
        for (int separator : separators) {
            if (seen.indexOf(separator) < 0) {
                continue;
            }
            List<String> pieces = partedAt(seen, separator);
            for (String witness : witnesses) {
                for (int at = 0; at < pieces.size(); at++) {
                    List<String> put = new ArrayList<>(pieces);
                    put.set(at, witness);
                    add(out, joined(put, separator), seen);
                }
                add(out, joined(pieces.stream().map(_ -> witness).toList(), separator), seen);
            }
        }
        return out;
    }

    private static void add(List<String> out, String candidate, String seen) {
        if (!candidate.equals(seen) && !out.contains(candidate)) {
            out.add(candidate);
        }
    }

    private static List<String> partedAt(String text, int separator) {
        List<String> pieces = new ArrayList<>();
        StringBuilder piece = new StringBuilder();
        text.codePoints().forEach(each -> {
            if (each == separator) {
                pieces.add(piece.toString());
                piece.setLength(0);
            } else {
                piece.appendCodePoint(each);
            }
        });
        pieces.add(piece.toString());
        return pieces;
    }

    private static String joined(List<String> pieces, int separator) {
        return String.join(new String(Character.toChars(separator)), pieces);
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof StringDemands that && separators.equals(that.separators)
                && attempted.equals(that.attempted);
    }

    @Override
    public int hashCode() {
        return 31 * separators.hashCode() + attempted.hashCode();
    }

    @Override
    public String toString() {
        return "StringDemands[separators=" + separators + ", attempted=" + attempted + "]";
    }
}
