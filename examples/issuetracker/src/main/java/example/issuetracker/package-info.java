/**
 * The types ({@code Issue} / {@code Label} / {@code LabelSet} / {@code LabelCounts} / …) and behaviors
 * ({@code openIssue} / {@code findIssue} / {@code attachLabel} / {@code detachLabel} /
 * {@code sharedLabels} / {@code assigneeOf} / {@code countByLabel} / {@code topLabels}) in this package
 * are generated at compile time by {@code SoutherProcessor} from {@code src/main/souther/issues.sou}.
 * This {@code package-info} is the one minimal Java source that makes javac run annotation processing
 * (it will not without at least one source) — which is also what puts the generated classes in
 * {@code target/classes} before kotlinc compiles the boundary against them.
 */
package example.issuetracker;
