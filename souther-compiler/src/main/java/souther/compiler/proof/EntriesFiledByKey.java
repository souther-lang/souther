package souther.compiler.proof;

import souther.compiler.core.TheWalk;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.BindingId;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * Which operations the library defines answer a map holding each element of a list, under the key
 * a closure makes of it — and which of their arguments are that closure and that list — read off
 * their bodies.
 *
 * <p>An operation is one where its body walks the list from an empty map, filing each element under
 * the key the closure answers on it, in place of what was filed under that key before. What that
 * licenses is what the two kernel operations it is written with say of themselves and nothing
 * else: {@code Map.insert} files a value under a key and changes no other key's, so the answer
 * holds, under every key some element has, the last element to have it, and no other entry.
 *
 * <p>Read off the body so that an operation written beside them in the library is read as the one it
 * is, whatever it is called.
 */
public final class EntriesFiledByKey {

    /**
     * Where the arguments of an operation filing each element of a list under a key are.
     *
     * @param keyArg    the closure that answers the key an element is filed under
     * @param walkedArg the list whose elements are filed
     */
    public record Filing(int keyArg, int walkedArg) {}

    private EntriesFiledByKey() {}

    /** The operations among {@code stdlib}'s helpers that file each element under its key, read
     *  as {@code library} declares the operations they are written with. */
    public static Map<ValueName.Stdlib.Operation, Filing> of(Stdlib stdlib, Library library) {
        Map<ValueName.Stdlib.Operation, Filing> filings = new LinkedHashMap<>();
        stdlib.helpers().forEach((operation, declaration) -> {
            Filing read = readOff(LibraryTerms.of(stdlib, declaration), stdlib.walk(), library);
            if (read != null) {
                filings.put(operation, read);
            }
        });
        return Map.copyOf(filings);
    }

    /** The filing {@code body} is, or null where it is none. */
    private static Filing readOff(LibraryTerm body, TheWalk walk, Library library) {
        if (!(body instanceof LibraryTerm.Call(var walks, List<LibraryTerm> args))
                || !walks.equals(walk.operation()) || args.size() != library.takes(walks).size()
                || !(args.get(walk.index()) instanceof LibraryTerm.WholeNumber(long from))
                || from != 0
                || !(args.get(walk.step()) instanceof LibraryTerm.Closure(List<BindingId> params,
                        LibraryTerm step))
                || params.size() != 2
                || !(args.get(walk.seed()) instanceof LibraryTerm.Call(var seed,
                        List<LibraryTerm> none))
                || !library.answersNothing(seed) || !none.isEmpty()
                || !(args.get(walk.container()) instanceof LibraryTerm.Parameter(int walked))
                || !(step instanceof LibraryTerm.Call(var filing, List<LibraryTerm> filed))
                || !(library.puts(filing) instanceof Library.Put(int value, int into,
                        Optional<Integer> under))
                || under.isEmpty()) {
            return null;
        }
        BindingId accumulator = params.get(walk.accumulator());
        BindingId element = params.get(walk.element());
        // The key is what a closure given the element answers, the value is the element itself,
        // and the map it is filed in is the one so far.
        if (!(filed.get(under.get()) instanceof LibraryTerm.Applied(
                        LibraryTerm function, List<LibraryTerm> appliedTo))
                || !(function instanceof LibraryTerm.Parameter(int key))
                || appliedTo.size() != 1
                || !(appliedTo.getFirst() instanceof LibraryTerm.Bound(BindingId keyed))
                || !keyed.equals(element)
                || !(filed.get(value) instanceof LibraryTerm.Bound(BindingId held))
                || !held.equals(element)
                || !(filed.get(into) instanceof LibraryTerm.Bound(BindingId carried))
                || !carried.equals(accumulator)) {
            return null;
        }
        return new Filing(key, walked);
    }
}
