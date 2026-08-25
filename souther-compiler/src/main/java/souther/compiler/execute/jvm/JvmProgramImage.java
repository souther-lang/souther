package souther.compiler.execute.jvm;

import souther.compiler.generated.EvaluationArtifact;
import souther.compiler.meta.PublishedClasses;

import java.util.function.Supplier;

/**
 * The program an evaluation runs against, in the terms the JVM implementation runs it in.
 *
 * <p>Its own type rather than the emitted artifact passed along. What a compile emits is a shape
 * this compiler and its backend agree on today; what a run needs is a program to run, a place to
 * resolve the rest of the world in, and a way to read what a module published. Naming the second in
 * terms of the first would make one emission's shape the standing contract of this seam.
 *
 * @param program      the classes to run, with what the compile implemented among them, from the one
 *                     emission that decided both
 * @param around       what the program is resolved against — the path's classes, defined here and
 *                     counted on the way in, so one binary name is one type
 * @param published    what this compile can read declarations of, asked for only if an answer has to
 *                     be held to something
 */
public record JvmProgramImage(EvaluationArtifact program, ClassLoader around,
                              Supplier<PublishedClasses> published) {

    public JvmProgramImage {
        if (program == null || around == null || published == null) {
            throw new IllegalArgumentException("a program to run is all three");
        }
    }
}
