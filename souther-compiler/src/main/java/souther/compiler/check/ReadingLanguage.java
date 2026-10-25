package souther.compiler.check;

/**
 * Which of the readings a fact about a clause is a fact of.
 *
 * <p>A name and nothing else. Nothing of this type is ever made — what it is for is standing in the
 * type of a value so that a fact one reading worked out cannot be handed to the other. The two are
 * short of different things ({@link Confinement}): which values may stand at a position is a set
 * and where its order stops is a range, and neither has a word for what the other holds. So a
 * position one of them says a choice left open is not a position the other says anything about, and
 * a value carrying such an answer is only meaningful beside the reading that gave it.
 *
 * <p><b>Which the type says rather than a comment.</b> Both answers are sets of positions, so the
 * two are the same Java type once the tag is dropped and either can be passed where the other
 * belongs. What that costs is not an exception: the reading that receives the wrong answer composes
 * it perfectly happily and reports a clause it read as one it did not.
 *
 * <p>The tag is on the answer and on what consumes it, so an accidental crossing does not compile.
 * It does not make the underlying set of positions a different type: written out, the positions of
 * one language's answer can still be put in a value tagged as the other's. What is closed is
 * handing one to the other, which is the way the two meet in an expression.
 */
sealed interface ReadingLanguage {

    /** The reading that says which values may stand at a position. */
    final class Values implements ReadingLanguage {

        private Values() {}
    }

    /** The reading that says where a position's order stops. */
    final class Order implements ReadingLanguage {

        private Order() {}
    }

    /**
     * The reading that says where a number an operation answers of a position stops
     * ({@link BoundaryReading}).
     *
     * <p>A third account and not a part of the second. {@code String.length(value) == 3} names no
     * end of the position's own order and leaves no set of strings the values reading can build, and
     * it is read whole as the one length it leaves.
     */
    final class DerivedNumbers implements ReadingLanguage {

        private DerivedNumbers() {}
    }

    /**
     * The reading that says how the elements of a container stand to each other
     * ({@link ElementsApart}).
     *
     * <p>A fourth account, and no part of the values reading. {@code List.allDistinctBy(.id, value)}
     * leaves every list whose elements' keys are pairwise apart, which no set of the position's
     * values says: the values reading still holds every list there, and is right to, since a set
     * that held the rule would have to hold two lists apart by what is inside them. What this one
     * says is that the rule was read whole — the containers it admits are the ones whose builders
     * keep the elements apart, and each element still takes every value.
     *
     * <p>And how a map's entries stand to a key beside it ({@link EntryHeld}): the map is taken in
     * at the map and at the key, since the rule is about the two together and the builders of the
     * record choose the key first and build the map holding the entry under it.
     */
    final class Elements implements ReadingLanguage {

        private Elements() {}
    }
}
