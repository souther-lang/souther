package souther.compiler.proof;

import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.BindingId;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Which operations the library defines file one value under one key of a map and leave every other
 * key as it was — and which of their arguments are that key, the value filed where the key was
 * absent, the closure that rewrites the value where it was present, and the map — read off their
 * bodies.
 *
 * <p>An operation is one where its body looks the key up and answers the map with that key's value
 * replaced: the value the closure makes of the one found where there is one, and the argument it
 * was given for the absent case where there is none. What that licenses is what the two kernel
 * operations it is written with say of themselves and nothing else. {@code Map.get} answers the
 * value filed under the key, where there is one; {@code Map.insert} files a value under a key in
 * place of what was there and changes no other key's value. So the answer holds, under the key, what
 * the closure made of the old value or the absent argument, and under every other key what it held
 * before.
 *
 * <p>Read off the body so that an operation written beside them in the library is read as the one it
 * is, whatever it is called.
 */
public final class KeyedUpdates {

    /**
     * Where the arguments of an operation filing one value under a key are.
     *
     * @param keyArg     the key the value is filed under
     * @param absentArg  the value filed where the key had none
     * @param closureArg the closure applied to the value found where it had one
     * @param mapArg     the map the answer is made from
     */
    public record Update(int keyArg, int absentArg, int closureArg, int mapArg) {}

    private static final ValueName.Stdlib.Operation GET = ValueName.Stdlib.operation("Map", "get");

    private static final ValueName.Stdlib.Operation INSERT =
            ValueName.Stdlib.operation("Map", "insert");

    private KeyedUpdates() {}

    /** The operations among {@code library}'s helpers that file one value under one key. */
    public static Map<ValueName.Stdlib.Operation, Update> of(Stdlib library) {
        Map<ValueName.Stdlib.Operation, Update> updates = new LinkedHashMap<>();
        library.helpers().forEach((operation, declaration) -> {
            Update read = readOff(LibraryTerms.of(library, declaration));
            if (read != null) {
                updates.put(operation, read);
            }
        });
        return Map.copyOf(updates);
    }

    /** The update {@code body} is, or null where it is none. */
    private static Update readOff(LibraryTerm body) {
        if (!(body instanceof LibraryTerm.OnAnOption(LibraryTerm option, BindingId found,
                LibraryTerm present, LibraryTerm absent, var _))
                || !(option instanceof LibraryTerm.Call(var looked, List<LibraryTerm> lookedAt))
                || !looked.equals(GET) || lookedAt.size() != 2
                || !(lookedAt.get(0) instanceof LibraryTerm.Parameter(int key))
                || !(lookedAt.get(1) instanceof LibraryTerm.Parameter(int map))) {
            return null;
        }
        // The key filed where the value was found, with what the closure made of the value found.
        List<LibraryTerm> presented = insertedInto(present, key, map);
        if (presented == null
                || !(presented.get(1) instanceof LibraryTerm.Applied(
                        LibraryTerm function, List<LibraryTerm> appliedTo))
                || !(function instanceof LibraryTerm.Parameter(int closure))
                || appliedTo.size() != 1
                || !(appliedTo.getFirst() instanceof LibraryTerm.Bound(BindingId bound))
                || !bound.equals(found)) {
            return null;
        }
        // And filed where there was none, with the argument given for that case.
        List<LibraryTerm> missing = insertedInto(absent, key, map);
        if (missing == null || !(missing.get(1) instanceof LibraryTerm.Parameter(int whenAbsent))) {
            return null;
        }
        return new Update(key, whenAbsent, closure, map);
    }

    /**
     * The arguments of {@code term}, where it files a value under the argument {@code key} of the
     * map the argument {@code map} is — or null where it is anything else.
     */
    private static List<LibraryTerm> insertedInto(LibraryTerm term, int key, int map) {
        return term instanceof LibraryTerm.Call(var operation, List<LibraryTerm> args)
                && operation.equals(INSERT) && args.size() == 3
                && args.get(0) instanceof LibraryTerm.Parameter(int at) && at == key
                && args.get(2) instanceof LibraryTerm.Parameter(int into) && into == map
                ? args : null;
    }
}
