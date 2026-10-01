package souther.runtime;

import java.lang.invoke.MethodHandles;
import java.util.List;
import java.util.function.Predicate;
import net.unit8.notation199x.pattern.StringPattern;

/**
 * The patterns a generated class runs: {@code String.matches} and a decoder's format constraint.
 *
 * <p>The compiler reads a pattern, builds the machine it means, and writes the machine into the
 * class as an image; what the class loads is that image, through {@link #read}. So nothing at run
 * time decides what a pattern means, and no engine's way of finding a match is involved in the
 * answer.
 *
 * <p>The constant is a {@code Predicate} and not the type that runs it, so a generated class names
 * this class and the JDK, and nothing of the library the machine is run by. What that leaves to the
 * library is the image, and an image says which format it is written in. A release of the library
 * reads every format an earlier release wrote, and refuses a format it does not read, saying which
 * it was given. So a class runs against the release it was compiled with or a later one, and
 * against an earlier one that does not read its image it is refused where the constant is loaded;
 * it is never run as some other machine.
 */
public final class Patterns {

    private Patterns() {}

    /**
     * The strings an image accepts, for a class loading the constant it was written as.
     *
     * <p>The bootstrap of that constant. The class holds the image as the strings it was cut into,
     * and the JVM resolves the constant once and answers from its pool afterwards.
     */
    public static Predicate<String> read(MethodHandles.Lookup lookup, String name, Class<?> type,
                                         String... image) {
        return StringPattern.of(List.of(image));
    }
}
