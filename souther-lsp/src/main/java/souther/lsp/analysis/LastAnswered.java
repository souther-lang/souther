package souther.lsp.analysis;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

/**
 * What the compiler last said about a document, kept for while it cannot say anything about it.
 *
 * <p>A document that will not parse is held out of the compile, and that is the document being typed
 * in — so every question answered from the compile goes unanswerable at the keystroke that starts
 * the edit it was there to help with. What is kept here is the last answer, offered until there is a
 * new one.
 *
 * <p>An availability fallback and not a second source. It is written only where the compiler
 * answered and read only where it did not, and the two are never merged, so what a reader gets is
 * either what this compile says or what the last one did — never half of each. That is what makes a
 * deletion take effect the moment the document parses again.
 *
 * <p>Per document rather than per module, because a module is not one file. Seen from an attached
 * {@code examples for} file, what its module's own source declares is from elsewhere, and a
 * partition drawn at the module would drop exactly that while the other file is the one being
 * edited.
 *
 * <p>The mechanism only. What is worth remembering, and what counts as the compiler having nothing
 * to say, is each reader's own — they answer it by what they hand over and by handing over nothing.
 */
final class LastAnswered<T> {

    /** An answer, and what it was an answer about. */
    private record Answered<V>(String subject, V value) {}

    private final Map<String, Answered<T>> byDocument = new LinkedHashMap<>();

    /**
     * What {@code ask} answers about {@code uri}, or what it last answered where it answers nothing
     * now and was answering about the same thing.
     *
     * <p>{@code subject} is what the answer is about — the module a document belongs to — and null
     * where that is not known either. A document is edited while it is a document of one module, and
     * what is kept is an answer about that module; a document that has become another module's has
     * no last answer, since the one being kept was never about what is being asked. Falling back
     * without asking would be handing over a declaration of a module this file no longer has
     * anything to do with.
     *
     * <p>An unknown subject falls back. Which module a document belongs to is itself the compile's
     * answer and goes absent with everything else, so refusing there would refuse in exactly the
     * case this is for.
     *
     * <p>Null where nothing has been answered about this document that this asking may have: there
     * is nothing to fall back to, and a reader with nothing to say says nothing rather than
     * something it did not read.
     */
    T of(String uri, String subject, Supplier<T> ask) {
        T answered = ask.get();
        if (answered != null) {
            byDocument.put(uri, new Answered<>(subject, answered));
            return answered;
        }
        Answered<T> kept = byDocument.get(uri);
        if (kept == null) {
            return null;
        }
        boolean aboutTheSame =
                subject == null || kept.subject() == null || subject.equals(kept.subject());
        return aboutTheSame ? kept.value() : null;
    }

    /** Forgets every document the workspace no longer holds, so a file that was deleted or renamed
     * leaves nothing behind. */
    void forgetAllBut(Collection<String> uris) {
        byDocument.keySet().retainAll(Set.copyOf(uris));
    }
}
