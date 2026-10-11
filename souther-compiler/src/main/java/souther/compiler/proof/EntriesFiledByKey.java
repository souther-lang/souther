package souther.compiler.proof;

import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.BindingId;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

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

    /** The walk a {@code fold} is written as, handed the index it starts at. */
    private static final ValueName.Stdlib.Operation FOLD_FROM =
            ValueName.Stdlib.operation("List", "foldFrom");

    private static final ValueName.Stdlib.Operation EMPTY =
            ValueName.Stdlib.operation("Map", "empty");

    private static final ValueName.Stdlib.Operation INSERT =
            ValueName.Stdlib.operation("Map", "insert");

    private EntriesFiledByKey() {}

    /** The operations among {@code library}'s helpers that file each element under its key. */
    public static Map<ValueName.Stdlib.Operation, Filing> of(Stdlib library) {
        Map<ValueName.Stdlib.Operation, Filing> filings = new LinkedHashMap<>();
        library.helpers().forEach((operation, declaration) -> {
            Filing read = readOff(LibraryTerms.of(library, declaration));
            if (read != null) {
                filings.put(operation, read);
            }
        });
        return Map.copyOf(filings);
    }

    /** The filing {@code body} is, or null where it is none. */
    private static Filing readOff(LibraryTerm body) {
        if (!(body instanceof LibraryTerm.Call(var walk, List<LibraryTerm> args))
                || !walk.equals(FOLD_FROM) || args.size() != 4
                || !(args.get(3) instanceof LibraryTerm.WholeNumber(long from)) || from != 0
                || !(args.get(0) instanceof LibraryTerm.Closure(List<BindingId> params,
                        LibraryTerm step))
                || params.size() != 2
                || !(args.get(1) instanceof LibraryTerm.Call(var seed, List<LibraryTerm> none))
                || !seed.equals(EMPTY) || !none.isEmpty()
                || !(args.get(2) instanceof LibraryTerm.Parameter(int walked))
                || !(step instanceof LibraryTerm.Call(var filing, List<LibraryTerm> filed))
                || !filing.equals(INSERT) || filed.size() != 3) {
            return null;
        }
        BindingId accumulator = params.get(0);
        BindingId element = params.get(1);
        // The key is what a closure given the element answers, the value is the element itself,
        // and the map it is filed in is the one so far.
        if (!(filed.get(0) instanceof LibraryTerm.Applied(
                        LibraryTerm function, List<LibraryTerm> appliedTo))
                || !(function instanceof LibraryTerm.Parameter(int key))
                || appliedTo.size() != 1
                || !(appliedTo.getFirst() instanceof LibraryTerm.Bound(BindingId keyed))
                || !keyed.equals(element)
                || !(filed.get(1) instanceof LibraryTerm.Bound(BindingId value))
                || !value.equals(element)
                || !(filed.get(2) instanceof LibraryTerm.Bound(BindingId into))
                || !into.equals(accumulator)) {
            return null;
        }
        return new Filing(key, walked);
    }
}
