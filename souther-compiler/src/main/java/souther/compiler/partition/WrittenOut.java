package souther.compiler.partition;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

/**
 * What a template means at a parameter: the value it builds, written out the way a row would write
 * it ({@link FixtureTemplate#meaning}).
 *
 * <p>Bound to the subject and the check of one run, which is the scope the answers hold in: the
 * build of a template at a parameter, and the writing out of what was built, are the same each
 * time a candidate names it there. Worked out once per template and parameter, because a search
 * names the same few stated values in every candidate it takes.
 *
 * <p>A template nothing built, or whose build cannot be written out, means its own spelling, so a
 * value that could not be read is never taken for another. That is remembered too: the build is
 * the run's own answer and asking again would give it again.
 *
 * <p>Only the templates this search writes against a value the module states are given a meaning
 * here. Every other template means its own spelling, which is the spelling the generator wrote it
 * in and the only one it writes it in; a value is told from another by its meaning where a stated
 * value is in play, and by nothing the generator could have written two ways elsewhere.
 */
final class WrittenOut {

    /** For a run with no runtime to build against: every template means its own spelling. */
    static final WrittenOut NOTHING_TO_BUILD = new WrittenOut(null, null);

    private record At(int parameter, String spelling) {}

    private final MeasuredInput subject;

    private final Generator.CandidateCheck check;

    private final Map<At, Optional<String>> meant = new HashMap<>();

    WrittenOut(MeasuredInput subject, Generator.CandidateCheck check) {
        this.subject = subject;
        this.check = check;
    }

    /** {@code template}, meaning what it builds at {@code parameter} written out. */
    FixtureTemplate of(int parameter, FixtureTemplate template) {
        if (check == null) {
            return template;
        }
        return meant.computeIfAbsent(new At(parameter, template.text()),
                        _ -> writtenOut(parameter, template))
                .map(template::meaningAs).orElse(template);
    }

    private Optional<String> writtenOut(int parameter, FixtureTemplate template) {
        return check.build(parameter, template)
                instanceof Generator.CandidateCheck.Built.Value(var value)
                ? SeedFixtures.written(value, subject.types().get(parameter), subject.ruleReading())
                        .map(FixtureTemplate::text)
                : Optional.empty();
    }
}
