package souther.compiler.query;

import souther.compiler.jvm.ClassFileImage;

import java.util.Map;
import java.util.function.Supplier;

/**
 * The loader over one set of class files, kept for as long as those are the class files.
 *
 * <p>A class is its binary name and the loader that defined it, so two loaders over one program are
 * two definitions of every type in it, and a value made under the first is not a value of the
 * second's. What that looks like is not an exception: a decoded key stops equalling the key a
 * behavior looks up, the lookup misses, and the behavior answers with its default — a correct model
 * reported as one whose example does not hold.
 *
 * <p><b>Which classes there are is asked by what they say.</b> A generation that ran again and came
 * to the same class files is the same program, and a loader made afresh over it would divide the
 * types of a program nothing about had changed. Being the same map is a shortcut past the
 * comparison and never the reason for the answer — asking which object the map is would answer a
 * question about a program with where the answer came from, which is the mistake
 * {@link ClassFileImage} exists to stop one level down.
 *
 * <p><b>A thing of its own rather than a condition inside whoever caches.</b> Written as a branch in
 * the method that hands out a loader, the rule can only be reached by whatever produces two class
 * sets, and a rule nothing can ask on its own is one nothing can be held to on its own: the branch
 * that keeps a loader over classes that were built again is exactly the one no ordinary edit
 * reaches. Here it is a unit two class sets can be handed.
 */
final class LoaderOverClasses {

    /** The classes the loader below was made over, or null where there is no loader yet. */
    private Map<String, ClassFileImage> over;
    private ClassLoader loader;

    /**
     * The loader over {@code classes}: the one already held where those are still the classes, and
     * otherwise one {@code build} makes.
     *
     * <p>Built before either field is written, so a build that raised leaves this holding what it
     * held rather than classes it did not manage to make a loader for. Recording them first would
     * leave the two saying different things, and the next ask would read that as a loader it
     * already has — handing out the one from before the edit.
     */
    ClassLoader of(Map<String, ClassFileImage> classes, Supplier<ClassLoader> build) {
        if (loader != null && theSameClasses(over, classes)) {
            return loader;
        }
        ClassLoader built = build.get();
        over = classes;
        loader = built;
        return built;
    }

    /**
     * Whether these are the same classes, which is whether they are the same class files.
     *
     * <p>The identity is asked first and is an answer to nothing: two names for one map are the
     * same classes, and it saves comparing what the map holds. Two maps that hold the same class
     * files are the same classes just as much.
     */
    static boolean theSameClasses(Map<String, ClassFileImage> one,
                                  Map<String, ClassFileImage> other) {
        return one == other || (one != null && one.equals(other));
    }
}
