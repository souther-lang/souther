package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.values.AuthoredOccurrence;

import java.util.IdentityHashMap;
import java.util.Map;

/**
 * One {@link AuthoredOccurrence} per node of a clause, and the same one every time that node is
 * read.
 *
 * <p>By the node itself and not by what a node is equal to. Two conjuncts written the same way are
 * two places in a clause, which is the rule the parts of a reading are already filed under
 * ({@code StatedByClauses.Said}); this is that same rule made into something a reading can hand
 * across to whatever makes machines.
 *
 * <p><b>Kept rather than made on the way past.</b> A clause is read more than once — once for the
 * declaration and once for the rule it belongs to — and a token minted at each visit would say two
 * readings of one pattern are two places somebody wrote. What is wanted is the written thing, so
 * what answers is a table and not a constructor.
 *
 * <p>Nothing here decides what a part is. Which node a reader is sent to for a refusal is settled
 * where the parts are, by the node being inside one; this is only what lets the refusal name a node
 * at all, out where a node is not a thing anybody has.
 */
final class AuthoredOccurrences {

    private final Map<Core, AuthoredOccurrence> byNode = new IdentityHashMap<>();

    /** The occurrence of {@code e}, made the first time it is asked for and kept. */
    AuthoredOccurrence of(Core e) {
        return byNode.computeIfAbsent(e, _ -> AuthoredOccurrence.another());
    }
}
