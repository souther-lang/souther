package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.proof.LibraryTerm;
import souther.compiler.proof.LibraryTerms;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;

/**
 * The operations of a library whose proofs come out as the shipped library's do, so that what
 * proving them came to when this compiler was built is what proving them here comes to.
 *
 * <p>A proof of what is stated of an operation reads the operation as the proofs read a body
 * ({@link LibraryTerms}), with its signature and its kernel, and reads the same of each operation
 * the body calls, through their bodies in turn; of the library as a whole it reads the walk and the
 * sugars. Two libraries alike in the whole are alike for an operation wherever they are alike in
 * that operation and in everything it calls, followed to the end. An operation calling one whose
 * body changed is not alike, and is proved again with it.
 *
 * <p>What a proof reads of a body is a value with no position in it, so a rewrite that moves the
 * text of one operation leaves every other operation of the file as it was.
 */
final class WhatALibraryLeavesAsShipped {

    /** What a proof reads of one operation itself: null for a body it has none of. */
    private record Read(LibraryTerm body, Stdlib.Signature signature, Stdlib.Intrinsic intrinsic) {}

    /** What a proof reads of each operation of {@code library}. */
    private static Map<ValueName.Stdlib.Operation, Read> readsOf(Stdlib library) {
        Map<ValueName.Stdlib.Operation, Read> out = new LinkedHashMap<>();
        library.entries().forEach((operation, entry) -> {
            var declaration = library.helpers().get(operation);
            out.put(operation, new Read(
                    declaration == null ? null : LibraryTerms.of(library, declaration),
                    entry.signature(), library.intrinsicOf(operation)));
        });
        return out;
    }

    private static final class Shipped {
        private static final Stdlib LIBRARY = DefaultStdlib.get();
        private static final Map<ValueName.Stdlib.Operation, Read> READS = readsOf(LIBRARY);
    }

    private WhatALibraryLeavesAsShipped() {
    }

    /**
     * Whether each operation of {@code library} is proved as the shipped library's is: everywhere
     * for the shipped library itself, and nowhere for a library whose walk, sugars or operations
     * are other than the shipped one's.
     */
    static Predicate<ValueName.Stdlib.Operation> of(Stdlib library) {
        if (library == Shipped.LIBRARY) {
            return _ -> true;
        }
        if (!library.walk().equals(Shipped.LIBRARY.walk())
                || !library.rewrites().equals(Shipped.LIBRARY.rewrites())
                || !library.entries().keySet().equals(Shipped.READS.keySet())) {
            return _ -> false;
        }
        Map<ValueName.Stdlib.Operation, Read> reads = readsOf(library);
        Set<ValueName.Stdlib.Operation> changed = new HashSet<>();
        reads.forEach((operation, read) -> {
            if (!read.equals(Shipped.READS.get(operation))) {
                changed.add(operation);
            }
        });
        Map<ValueName.Stdlib.Operation, Boolean> alike = new HashMap<>();
        return operation -> alike.computeIfAbsent(operation,
                from -> !reachesAnyOf(from, changed, reads));
    }

    /** Whether {@code from}, or anything its body calls followed to the end, is among
     *  {@code changed}. */
    private static boolean reachesAnyOf(ValueName.Stdlib.Operation from,
                                        Set<ValueName.Stdlib.Operation> changed,
                                        Map<ValueName.Stdlib.Operation, Read> reads) {
        Set<ValueName.Stdlib.Operation> seen = new LinkedHashSet<>();
        Deque<ValueName.Stdlib.Operation> next = new ArrayDeque<>();
        next.add(from);
        while (!next.isEmpty()) {
            ValueName.Stdlib.Operation operation = next.removeFirst();
            if (!seen.add(operation)) {
                continue;
            }
            if (changed.contains(operation)) {
                return true;
            }
            Read read = reads.get(operation);
            if (read != null && read.body() != null) {
                callsIn(read.body(), next);
            }
        }
        return false;
    }

    private static void callsIn(LibraryTerm term, Deque<ValueName.Stdlib.Operation> into) {
        if (term instanceof LibraryTerm.Call call) {
            into.add(Objects.requireNonNull(call.operation()));
        }
        LibraryTerm.forEachPart(term, part -> callsIn(part, into));
    }
}
