package souther.architecture;

/**
 * Where a model stands on the way to the place its report is read: whether the test is held to
 * its compiling by then.
 *
 * <p>Ordered by what can go wrong, so that where two ways meet the model stands as the worse of
 * what it stood as on each: asked about on one way and not on the other is a model that is not
 * known to have been asked about.
 */
enum ModelStanding {

    /** The helper was handed it, so the test stops if it does not compile. */
    ASKED,

    /** It came in as an argument of the method, which is asked about where the method is called. */
    HANDED_IN,

    /** It was made and nothing has been asked of it. */
    UNASKED,

    /** Where it came from cannot be told, so nothing can be said of it. */
    LOST;

    /** The worse of the two. */
    ModelStanding join(ModelStanding other) {
        return compareTo(other) >= 0 ? this : other;
    }
}
