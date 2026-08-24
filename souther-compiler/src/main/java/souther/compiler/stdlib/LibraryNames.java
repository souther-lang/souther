package souther.compiler.stdlib;

import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What resolving a module against the standard library takes: the type names the language declares
 * of its own, the operation names the library keeps to itself, the names it publishes as functions,
 * and what a bare spelling could have been reaching for.
 *
 * <p>Names and no declarations. Resolution decides what a spelling denotes, which these settle;
 * what is behind the name is a question for whoever holds the {@link Stdlib}, and a resolver given
 * the whole library could ask it questions that only make sense after resolution has finished.
 *
 * <p>Which is what {@link #ofTheLibraryBeingLoaded} is for. The library's own modules are resolved
 * before there is a library, and they are the one thing that can be said about them without one:
 * every module being resolved is inside the reserved namespace, so no name is one the library keeps
 * from it, and the types it may write are the ones collected from all of its modules. Said as a
 * value, so the resolver asks the same question of the library's sources as of anyone else's and
 * gets an answer that is true rather than one that is never reached.
 */
public record LibraryNames(Set<String> languageTypes, Set<String> privateOperations,
                           Set<String> operations, Map<String, List<String>> candidates) {

    public LibraryNames {
        languageTypes = Set.copyOf(languageTypes);
        privateOperations = Set.copyOf(privateOperations);
        operations = Set.copyOf(operations);
        candidates = Map.copyOf(candidates);
    }

    /** Whether {@code qualifiedName} is a standard-library function — a declared one, or a sugar
     *  for one. */
    public boolean isLibraryFunction(String qualifiedName) {
        return operations.contains(qualifiedName);
    }

    /** Every published name a bare {@code bareName} could be reaching for, or empty where the
     *  library publishes no such name. */
    public List<String> qualifiedCandidates(String bareName) {
        return candidates.getOrDefault(bareName, List.of());
    }

    /** Those candidates as a diagnostic writes them: {@code `Map.insert`, `Set.insert`}. The
     *  sentence they sit in belongs to the message catalog, so what is built here is the list and
     *  not a phrase — an "or" assembled in Java would be an English word in the Japanese report. */
    public String candidateList(String bareName) {
        StringBuilder sb = new StringBuilder();
        for (String qualified : qualifiedCandidates(bareName)) {
            if (!sb.isEmpty()) {
                sb.append(", ");
            }
            sb.append('`').append(qualified).append('`');
        }
        return sb.toString();
    }

    /** What the library's own sources are resolved against while it is being read: the types
     *  collected from all of its modules, and nothing else. No name is one the library keeps from
     *  them, because every module being resolved is inside the reserved namespace; no name is a
     *  library function yet, because that is what is being read; and there is no published surface
     *  to offer a bare spelling as a candidate from. */
    public static LibraryNames ofTheLibraryBeingLoaded(Set<String> languageTypes) {
        return new LibraryNames(languageTypes, Set.of(), Set.of(), Map.of());
    }
}
