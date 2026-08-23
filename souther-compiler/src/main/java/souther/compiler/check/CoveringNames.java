package souther.compiler.check;

import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * A set of values a subject can be, named the way the model declares them.
 *
 * <p>What a check decided over and what a report says it in are not the same thing. Exhaustiveness
 * is settled over the values a subject can be, because that is what an arm answers for and there is
 * no other set the arms can be compared on. A reader is not owed the answer in those terms: a model
 * that gave a group of cases a type of its own wrote that type to say something, and a report of
 * three leaves where the model would say one name is a report about a declaration nobody wrote.
 *
 * <p>So this names them back. A declared case all of whose values are in the set is named as itself;
 * one only partly in it is opened, and what is inside it is named the same way. Nothing is dropped
 * and nothing is added — the names that come out cover the set exactly.
 *
 * <p>Only a report reads this. It is the second reading of a question the check already answered,
 * which is exactly why it is here and not in the check: run the other way round — deciding over
 * declared cases and reporting leaves — the two would disagree about which programs compile, and
 * this way they can only disagree about how a refusal reads.
 */
final class CoveringNames {

    private CoveringNames() {}

    /**
     * {@code atoms} as the largest declared cases of {@code subject} that lie wholly inside it.
     *
     * <p>In the order the subject declares them, which is the order the model reads in. A value the
     * descent cannot reach a name for is named as itself, so what comes back covers the set however
     * odd the subject is.
     */
    static List<String> of(Type subject, List<TypeSymbol> atoms, Symbols symbols) {
        Set<TypeSymbol> left = new LinkedHashSet<>(atoms);
        List<String> named = new ArrayList<>();
        name(subject, left, symbols, named, new HashSet<>());
        for (TypeSymbol atom : left) {
            named.add(atom.name());
        }
        return named;
    }

    /**
     * Names what of {@code left} the cases of {@code subject} cover, taking what it names out of it.
     *
     * <p>Taken out as it goes, which is what keeps a value reached through two cases from being
     * named twice: a sum whose leaves two of its cases share would otherwise be reported as both of
     * them, and the second would be a name for values already accounted for.
     *
     * <p>{@code opened} is the cases already descended, which a sum reaching one case through two
     * others terminates on.
     */
    private static void name(Type subject, Set<TypeSymbol> left, Symbols symbols, List<String> out,
                             Set<TypeSymbol> opened) {
        for (ResolvedCase selected : CaseSpace.of(subject, symbols).selectors()) {
            if (left.isEmpty()) {
                return;
            }
            List<TypeSymbol> covers = selected.atoms();
            if (covers.isEmpty()) {
                continue;
            }
            if (left.containsAll(covers)) {
                out.add(selected.name().name());
                covers.forEach(left::remove);
            } else if (covers.stream().anyMatch(left::contains) && selected.bound() != null
                    && opened.add(selected.name())) {
                // Some of what it covers is missing and some is answered, so the case itself is not
                // what is missing — what is inside it is.
                name(selected.bound(), left, symbols, out, opened);
            }
        }
    }
}
