package souther.compiler.partition;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.stream.Collectors;

/**
 * What the measure made of one behavior of a module, written out for a test to compare.
 *
 * <p>The classes a rule parts a position into and what no reading took in, in one string. A
 * reading that gained a line by losing what it could not read is as wrong as one that read
 * nothing, and a test holding the two apart can assert one and forget the other.
 *
 * <p>The source is the caller's whole module. Which declarations a claim needs is part of the
 * claim, and a fixture shared between claims grows the declarations of each of them — after which
 * what a test compiles is no longer what it is about.
 */
final class MeasuredBehavior {

    /** The classes and the unread reasons of {@code behavior}, as {@code [classes] unread
     *  [reasons]}. */
    static String reading(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        AdequacyReport.BehaviorReport read = AdequacyReport.of(compilation)
                .modules().get(0).behaviors().stream()
                .filter(each -> each.name().equals(behavior)).findFirst().orElseThrow();
        return "[" + read.partition().axes().stream()
                .flatMap(axis -> axis.classes().stream())
                .collect(Collectors.joining(", "))
                + "] unread [" + read.partition().notRead().stream()
                .map(each -> each.at() + " " + each.reason())
                .collect(Collectors.joining(", ")) + "]";
    }

    private MeasuredBehavior() {}
}
