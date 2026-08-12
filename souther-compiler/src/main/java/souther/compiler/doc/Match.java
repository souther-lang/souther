package souther.compiler.doc;

import java.util.List;

/**
 * What counts as a document saying a term.
 *
 * <p>A phrase is a run of characters: a reader who types one is quoting the document, and where the
 * quoted run sits relative to the words around it is not something they said anything about. A word
 * is a word: {@code an} is not what {@code command} says, and a fallback that read it as one would
 * have its shortest words matching nearly every section and deciding the order of the answer.
 *
 * <p>Both corpora ask this rather than each spelling out its own comparison, because a search runs
 * over the two of them and sorts the result once. Two definitions of what a match is would put the
 * specification and a shipped topic on one list under two meanings of the number beside them.
 *
 * <p>Every text and every term reaching these is already folded to lower case by whoever holds it,
 * which for a document is once for the whole search rather than once for each term looked for in it.
 */
enum Match {

    /** Anywhere in the text, wherever the run of characters begins and ends. */
    ANYWHERE {
        @Override
        boolean at(String text, int found, int length) {
            return true;
        }
    },

    /** Only where the text has nothing but the term: no letter or digit either side of it. */
    WORD {
        @Override
        boolean at(String text, int found, int length) {
            return (found == 0 || !Character.isLetterOrDigit(text.charAt(found - 1)))
                    && (found + length == text.length()
                            || !Character.isLetterOrDigit(text.charAt(found + length)));
        }
    };

    /** Whether the run of {@code length} characters at {@code found} is the text saying the term. */
    abstract boolean at(String text, int found, int length);

    /**
     * How often {@code text} says {@code term}.
     *
     * <p>A term of no characters sits at every position and is said nowhere: a walk over its
     * occurrences would never advance past the first.
     */
    final int count(String text, String term) {
        if (term.isEmpty()) {
            return 0;
        }
        int said = 0;
        for (int at = text.indexOf(term); at >= 0; at = text.indexOf(term, at + term.length())) {
            if (at(text, at, term.length())) {
                said++;
            }
        }
        return said;
    }

    /** Whether {@code text} says {@code term} at all. */
    final boolean says(String text, String term) {
        return count(text, term) > 0;
    }

    /**
     * What a document holds of a query: whether what it is called is one of the terms, how many of
     * them it holds at all, and how often it says them.
     *
     * <p>{@code matched} before {@code occurrences} is the whole of why a query is one question. A
     * document holding four of the terms is a better answer than one saying the first of them forty
     * times, whichever of them the reader happened to type first.
     */
    record Held(boolean named, int matched, int occurrences) {}

    /**
     * What the document called {@code called} and saying {@code body} holds of {@code terms}.
     *
     * <p>One rule for every corpus a search spans, because the answers are merged and sorted once.
     * A specification section and a shipped topic scored by two rules would be placed against each
     * other by numbers that do not mean the same thing.
     */
    final Held held(String called, String body, List<String> terms) {
        boolean named = false;
        int matched = 0;
        int occurrences = 0;
        for (String term : terms) {
            boolean here = says(called, term);
            int said = count(body, term);
            named |= here;
            occurrences += said;
            if (here || said > 0) {
                matched++;
            }
        }
        return new Held(named, matched, occurrences);
    }
}
