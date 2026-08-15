package souther.compiler.examples;

import souther.compiler.meta.PublishedModule;

/**
 * Which declarations a value crossing into an answer is read by.
 *
 * <p>Not where the classes came from. How an implementation was carried in — a loader, a jar, an
 * artifact, something reached over a wire — is transport, and a run has no question about transport.
 * What it has a question about is which declarations the crossing is read by: a derived decoder
 * reads what its module's declarations said when it was built, so an answer built against an earlier
 * revision of the module reads a row's values by that revision. Two builds, one of them the module
 * the rows are written for and the other whatever the answer was compiled against.
 *
 * <p>So this is single however many pieces an implementation is assembled from. What a row's values
 * cross into is one set of declarations, and that is what is named here.
 *
 * <p>Two of them, and the difference is whether there is a second set at all. An answer of this
 * compile's has one — there are not two builds, so there is nothing to hold together and nothing is
 * read. An answer from outside carries the declarations its classes were stamped with, and a run
 * holds them against the module it is evaluating before handing it a row.
 */
public sealed interface Origin permits Origin.Published, TheCompilesOwn {

    /**
     * The declarations the answer's classes carry.
     *
     * <p>{@link PublishedModule.Classes} is how they are read and not what they are. What has to be
     * compared is what a crossing depends on, and that is a module's declarations however they are
     * carried — the same question would be asked of a digest, of a canonical form, of declarations
     * arriving some way class files are not involved in. This holds the reader that exists today,
     * and a reader that replaces it replaces this without the seam meaning anything different.
     *
     * @param classes where the declarations of the answer's module, and of the modules its
     *                declarations reach into, are read from
     */
    record Published(PublishedModule.Classes classes) implements Origin {}
}
