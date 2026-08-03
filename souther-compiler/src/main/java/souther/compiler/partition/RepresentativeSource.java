package souther.compiler.partition;

import java.util.List;

/**
 * The values that could stand for one equivalence class, in the order they should be tried.
 *
 * <p>More than one, because building a candidate can fail for a reason that is about the combination
 * and not about the class: two classes each covering a wide range, whose chosen representatives happen
 * to break a constraint that relates them. A generator that held one value per class would call that
 * combination impossible when another value would have built.
 *
 * <p>Empty where nothing can be produced. That is a fact about generation, not about the class — the
 * class is still counted, and rows that already reach it still count.
 */
@FunctionalInterface
public interface RepresentativeSource {

    List<FixtureTemplate> candidates();

    static RepresentativeSource of(FixtureTemplate... values) {
        List<FixtureTemplate> templates = List.of(values);
        return () -> templates;
    }

    static RepresentativeSource none() {
        return List::of;
    }
}
