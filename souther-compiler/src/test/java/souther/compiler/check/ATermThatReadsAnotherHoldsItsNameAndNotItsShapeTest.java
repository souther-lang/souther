package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a canonical key costs when the term it names reads a named value twice.
 *
 * <p>What terms are made of is a graph and not a tree. A name read twice is one value read twice, and
 * `+let (a, b) = t+` reads `+t+` twice by itself, so a chain of those is a graph whose nodes grow by
 * one per link and whose paths double. A key holding each of its parts in full holds one copy per
 * path — twenty-four links asked for more characters than an array can hold.
 *
 * <p>Held on the size of the key rather than on the time a compile takes. Time is what the growth
 * showed up as last: the chain measured flat right up to the link that asked for two gigabytes at
 * once, because the walk is one lookup per name and only what it wrote doubled. What was wrong is the
 * size of the representation, so that is what is measured, and it is measured where it is built.
 *
 * <p>Written as bindings, since that is where the sharing is. A value is read twice by being named
 * and read twice, not by a tree holding one node twice — which is also why the walk stayed linear
 * while the writing did not.
 */
class ATermThatReadsAnotherHoldsItsNameAndNotItsShapeTest {

    private static final SourcePos NOWHERE = new SourcePos(0, 0);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("m", "f");

    /** {@code v0 = 1 + 1}, then {@code v(i) = v(i-1) + v(i-1)}: each link names one value and reads
     *  it twice. Answers the key of the last link. */
    private static String chainKey(Terms terms, int links) {
        Denotations at = Denotations.none();
        Core value = new Core.Binary(Ast.BinOp.ADD, new Core.Int(1, Type.INT, NOWHERE),
                new Core.Int(1, Type.INT, NOWHERE), Type.INT, NOWHERE);
        String key = terms.bodyKey(value, at);
        for (int i = 0; i < links; i++) {
            BindingId id = new BindingId(OWNER, i);
            at = at.binding(id, value, new Denotes.Term(key, true));
            Core read = new Core.Read("v" + i, id, Type.INT, NOWHERE);
            value = new Core.Binary(Ast.BinOp.ADD, read, read, Type.INT, NOWHERE);
            key = terms.bodyKey(value, at);
        }
        return key;
    }

    private static int keyLength(int links) {
        String key = chainKey(new Terms(Symbols.none()), links);
        return key == null ? -1 : key.length();
    }

    /**
     * A link adds a name to read, and a name is what a link adds.
     *
     * <p>Asked at four lengths as one map, because what is held is that the number does not follow the
     * chain — one length is met by any growth at all, and it was met by one that doubled.
     */
    @Test
    void aLinkCostsTheSameWhateverIsUnderIt() {
        // Asked shortest first and held as it goes, so that a key which follows the chain is caught
        // at the length where it is still a number and not at the one where it is an allocation.
        Map<Integer, Integer> measured = new LinkedHashMap<>();
        for (int links : List.of(4, 8, 16, 32)) {
            int length = keyLength(links);
            measured.put(links, length);
            assertTrue(length > 0 && length <= 16,
                    "a key names one shape and is read as a name: " + measured);
        }
    }

    /**
     * The chain a compile met, at a length the growth never allowed.
     *
     * <p>Twenty-four links is where it stopped, having asked for two gigabytes. A thousand is past
     * every length that was reachable, and the key is still a name.
     */
    @Test
    void aChainLongerThanTheOldLimitIsStillOneName() {
        assertTrue(keyLength(1000) <= 16, "the key at a thousand links: " + keyLength(1000));
    }

    /**
     * Naming a shape does not merge two shapes that differ.
     *
     * <p>Which is the property the keys are for: two terms are one key exactly when they compute one
     * value, and that is what makes naming an expression not change what is known of it. A chain of
     * four and a chain of five read alike at every link but the last.
     */
    @Test
    void twoShapesThatDifferAreTwoNames() {
        Terms terms = new Terms(Symbols.none());
        String four = chainKey(terms, 4);
        String five = chainKey(terms, 5);
        String fourAgain = chainKey(terms, 4);

        assertEquals(four, fourAgain, "one shape is one name");
        assertNotEquals(four, five, "and two shapes are two");
    }
}
