package souther.compiler.query;

import souther.compiler.types.TypeKey;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The questions a store is asked about one declaration are filed apart from each other.
 *
 * <p>Each of them is a record whose one component is the declaration's address, so their own hashes
 * are the address's and are all the same. Filed by those, a store holding every question about a
 * declaration holds them in one bucket and compares them one by one on every ask. The store files a
 * question by what it asks as well as what it is about.
 */
class TheQuestionsAboutOneDeclarationAreFiledApartTest {

    private static final TypeKey AMOUNT = new TypeKey("shop.prices", "Amount");

    private static final List<Key<?>> ABOUT_AMOUNT = List.of(
            new Names.Declaration(AMOUNT),
            new Names.DeclarationIsNewtype(AMOUNT),
            new Names.ResolvedDeclaration(AMOUNT),
            new Shapes.NewtypeInnerOf(AMOUNT),
            new Shapes.NewtypeTerminalOf(AMOUNT),
            new Shapes.MeaningOf(AMOUNT),
            new Shapes.FieldBindingsOf(AMOUNT),
            new Shapes.FieldLayoutOf(AMOUNT),
            new Shapes.NormalizedDef(AMOUNT));

    /** What the store is answering for: the questions' own hashes do not tell them apart. */
    @Test
    void theirOwnHashesAreAllTheSame() {
        assertEquals(1, ABOUT_AMOUNT.stream().map(Object::hashCode).distinct().count(),
                "each question's hash is its address's");
    }

    @Test
    void filedTheyHashApart() {
        Set<Integer> hashes = ABOUT_AMOUNT.stream()
                .map(key -> Db.Filed.of(key).hashCode())
                .collect(Collectors.toSet());

        assertEquals(ABOUT_AMOUNT.size(), hashes.size(), "one hash for each question");
    }

    /** And filing changes nothing about which question is which. */
    @Test
    void aQuestionFiledTwiceIsTheSameQuestion() {
        for (Key<?> key : ABOUT_AMOUNT) {
            assertEquals(Db.Filed.of(key), Db.Filed.of(key));
        }
        assertNotEquals(Db.Filed.of(new Shapes.NewtypeInnerOf(AMOUNT)),
                Db.Filed.of(new Shapes.NewtypeTerminalOf(AMOUNT)));
        assertTrue(Db.Filed.of(new Shapes.NewtypeInnerOf(AMOUNT))
                .equals(Db.Filed.of(new Shapes.NewtypeInnerOf(new TypeKey("shop.prices", "Amount")))));
    }
}
