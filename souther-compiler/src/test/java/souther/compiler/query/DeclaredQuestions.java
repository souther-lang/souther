package souther.compiler.query;

import java.lang.reflect.Modifier;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Stream;

/**
 * Every question this compiler declares, discovered from what it compiled to.
 *
 * <p>From the classes and not from a registry. A registry a key has to be added to is a second place
 * to keep in step, and the failure it allows is the one everything reading this exists to prevent: a
 * key added and not registered would leave every count over the vocabulary adding up while the
 * question went unwatched.
 *
 * <p><b>One perimeter for everything asked of the vocabulary.</b> Whether a question is reached, and
 * whether what it answers with can be compared as a value, are two claims about one set — and two
 * scans would be two sets, agreeing until the day one of them was taught something the other was
 * not. So the discovery is here and each claim says what it wants of what comes back.
 *
 * <p>The whole of what {@link Key} was compiled beside, and not a package under it. Any bound
 * narrower than that makes the count's own perimeter the thing that decides it: a key declared
 * outside would be in neither what is declared nor what is reached, and every equation over it would
 * go on balancing while the question went unwatched. Where a key is allowed to sit is a claim of its
 * own, and is
 * {@link EveryQuestionThisCompilerDeclaresIsReachedOrOutsideABatchRunTest#everyQuestionIsDeclaredWhereTheyBelong}'s
 * to make.
 */
final class DeclaredQuestions {

    /** Every concrete key this compiler was compiled with, and every class this could not load. */
    static Covered<Class<?>> scan() throws Exception {
        return scanOf(Path.of(
                Key.class.getProtectionDomain().getCodeSource().getLocation().toURI()));
    }

    /**
     * The same under {@code root}.
     *
     * <p>Takes where to look, so that what happens when a class will not load is something a test
     * can build rather than something nobody sees until it happens.
     */
    static Covered<Class<?>> scanOf(Path root) throws Exception {
        List<Class<?>> out = new ArrayList<>();
        List<Gap> gaps = new ArrayList<>();
        try (Stream<Path> files = Files.walk(root)) {
            for (Path each : files.filter(p -> p.toString().endsWith(".class")).toList()) {
                String name = root.relativize(each).toString()
                        .replace(java.io.File.separatorChar, '.')
                        .replaceFirst("\\.class$", "");
                Class<?> type;
                try {
                    type = Class.forName(name, false, Key.class.getClassLoader());
                } catch (Throwable notLoadable) {
                    // A class the scan found and cannot hold. Said out loud: skipped, it leaves the
                    // vocabulary smaller than it is and every count over it adds up over whatever
                    // is left.
                    gaps.add(new Gap(Gap.Why.A_CLASS_THAT_WOULD_NOT_LOAD,
                            name + " (" + notLoadable.getClass().getSimpleName() + ")"));
                    continue;
                }
                if (Key.class.isAssignableFrom(type) && !type.isInterface()
                        && !Modifier.isAbstract(type.getModifiers())) {
                    out.add(type);
                }
            }
        }
        out.sort(Comparator.comparing(Class::getName));
        return Covered.of(List.copyOf(out), gaps);
    }

    /** What was found, whether or not the scan read everything it met. */
    static List<Class<?>> found(Covered<Class<?>> covered) {
        return switch (covered) {
            case Covered.Whole<Class<?>>(List<Class<?>> all) -> all;
            case Covered.Partly<Class<?>>(List<Class<?>> all, List<Gap> _) -> all;
        };
    }

    private DeclaredQuestions() {
    }
}
