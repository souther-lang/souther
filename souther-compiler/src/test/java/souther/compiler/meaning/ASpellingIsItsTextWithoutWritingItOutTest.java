package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A spelling put together from pieces is the text those pieces write, to everything that tells two
 * apart or puts them in order: equal exactly where the texts are, hashing as the text hashes, and
 * ordered as {@link String#compareTo} orders the texts, to the value — however the two texts were cut
 * into pieces.
 *
 * <p>And a proposition nested as deep as a model nests its conditions holds its parts' spellings and
 * not a copy of them: built here thousands of levels deep over a part of ten thousand characters, it
 * would hold that part's text once for each level written out.
 */
class ASpellingIsItsTextWithoutWritingItOutTest {

    /** Characters that are ordered one way as {@code char}s and another as code points: the two
     *  halves of a surrogate pair stand below a character above them in the basic plane only as
     *  code points. */
    private static final String ALPHABET = "ab, [!]😀�";

    private record Spelled(Spelling spelling, String text) {}

    private static Spelled random(Random random, int depth) {
        if (depth == 0 || random.nextInt(3) == 0) {
            StringBuilder text = new StringBuilder();
            for (int i = random.nextInt(4); i > 0; i--) {
                text.append(ALPHABET.charAt(random.nextInt(ALPHABET.length())));
            }
            return new Spelled(Spelling.of(text.toString()), text.toString());
        }
        List<Spelling> pieces = new ArrayList<>();
        StringBuilder text = new StringBuilder();
        for (int i = 1 + random.nextInt(4); i > 0; i--) {
            Spelled piece = random(random, depth - 1);
            pieces.add(piece.spelling());
            text.append(piece.text());
        }
        return new Spelled(Spelling.joined(pieces), text.toString());
    }

    /** {@code text} cut into pieces at random places, some of them a level deeper. */
    private static Spelling cut(String text, Random random) {
        List<Spelling> pieces = new ArrayList<>();
        int at = 0;
        while (at < text.length()) {
            int next = Math.min(text.length(), at + 1 + random.nextInt(3));
            String piece = text.substring(at, next);
            pieces.add(random.nextBoolean() ? Spelling.of(piece)
                    : Spelling.joined(List.of(Spelling.of(piece.substring(0, 1)),
                            Spelling.of(piece.substring(1)))));
            at = next;
        }
        return Spelling.joined(pieces);
    }

    @Test
    void twoSpellingsCompareAsTheirTextsDo() {
        Random random = new Random(20261030L);
        List<Spelled> spelled = new ArrayList<>();
        for (int i = 0; i < 300; i++) {
            spelled.add(random(random, 4));
        }
        List<String> differ = new ArrayList<>();
        for (Spelled one : spelled) {
            if (!one.spelling().toString().equals(one.text())
                    || one.spelling().hashCode() != one.text().hashCode()
                    || one.spelling().length() != one.text().length()) {
                differ.add("written, hashed or measured otherwise: " + one.text());
            }
            for (Spelled other : spelled) {
                int expected = one.text().compareTo(other.text());
                if (one.spelling().compareTo(other.spelling()) != expected
                        || one.spelling().equals(other.spelling()) != (expected == 0)) {
                    differ.add(one.text() + " against " + other.text());
                }
            }
        }
        assertEquals(List.of(), differ.subList(0, Math.min(differ.size(), 5)));
    }

    /** One text cut two ways is one spelling, and a text one character longer is after it by the
     *  difference of the lengths, as String.compareTo answers. */
    @Test
    void whereTheTextIsCutDoesNotMatter() {
        Random random = new Random(20261031L);
        for (int i = 0; i < 200; i++) {
            String text = random(random, 3).text() + random(random, 3).text();
            Spelling one = cut(text, random);
            Spelling other = cut(text, random);
            assertEquals(one, other, text);
            assertEquals(0, one.compareTo(other), text);
            Spelling longer = Spelling.of(one, "a");
            assertEquals(text.compareTo(text + "a"), one.compareTo(longer), text);
            assertEquals((text + "a").compareTo(text), longer.compareTo(one), text);
        }
        Spelling ab = Spelling.of(Spelling.of("ab"), Spelling.of("c"));
        Spelling a = Spelling.of(Spelling.of("a"), Spelling.of("bd"));
        assertEquals("abc".compareTo("abd"), ab.compareTo(a));
    }

    /** Read a piece at a time with a stack of its own: a spelling nested deeper than a small
     *  thread's stack goes is compared, measured and written on that thread. */
    @Test
    void aSpellingDeeperThanTheStackIsReadWhole() throws InterruptedException {
        int depth = 20_000;
        Spelling one = Spelling.of("x");
        Spelling other = Spelling.of("x");
        for (int i = 0; i < depth; i++) {
            one = Spelling.of("(", one, ")");
            other = Spelling.of(Spelling.of("("), other, Spelling.of(")"));
        }
        String text = "(".repeat(depth) + "x" + ")".repeat(depth);
        Spelling deep = one;
        Spelling alike = other;
        List<Object> seen = new ArrayList<>();
        Thread small = new Thread(null, () -> {
            try {
                seen.add(deep.length());
                seen.add(deep.equals(alike));
                seen.add(deep.toString());
            } catch (StackOverflowError e) {
                seen.add(e);
            }
        }, "a small stack", 64 * 1024);
        small.start();
        small.join();
        assertEquals(List.of((long) text.length(), true, text), seen);
        assertEquals(text.hashCode(), deep.hashCode());
    }

    /** Turning a statement over and back writes nothing: the spelling of it holding is the one
     *  piece after the mark. */
    @Test
    void aDenialIsTheSpellingWithTheMarkBeforeIt() {
        Spelling held = Spelling.of("a < b");
        Spelling denied = Spelling.denying(false, held);
        assertEquals("!a < b", denied.toString());
        assertSame(held, denied.denied());
        assertEquals(denied, held.denied());
    }

    /** Conjunctions and disjunctions nested within one another: each level's spelling holds its
     *  parts' spellings themselves, so the text of a part is held once however many levels it is
     *  below, and is the text the level spells all the same. */
    @Test
    void aPropositionHoldsItsPartsSpellingsAndNotTheirText() {
        Proposition nested = new Proposition.Truth(
                new DecisionSubject.AnInput(TermPath.of("x".repeat(1_000))), true);
        List<String> copied = new ArrayList<>();
        for (int i = 0; i < 50; i++) {
            Proposition beside = new Proposition.Truth(
                    new DecisionSubject.AnInput(TermPath.of("p" + i)), true);
            Proposition below = nested;
            nested = i % 2 == 0 ? new Proposition.All(List.of(below, beside))
                    : new Proposition.Any(List.of(below, beside));
            if (!nested.spelling().holdsAsAPiece(below.spelling())
                    || !nested.spelling().holdsAsAPiece(beside.spelling())) {
                copied.add("level " + i);
            }
            assertEquals((i % 2 == 0 ? "all[" : "any[") + below.spelledOut() + ", "
                    + beside.spelledOut() + "]", nested.spelledOut());
        }
        assertEquals(List.of(), copied);
    }
}
