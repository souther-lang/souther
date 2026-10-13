package souther.cli.backend;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * What is said where a target's backend is neither installed nor fetched: each directory that was
 * searched and what it held, then what the repository answered.
 *
 * <p>Said as catalog keys and what fills them, one line each, so every language says every line.
 * Which of them a reader is shown does not depend on the language: a directory or an answer left
 * out of one would leave a reader of that language unable to tell a backend put in the wrong place
 * from one never installed.
 */
public final class Unavailable {

    private Unavailable() {}

    /** One line: a catalog key and what fills it. */
    public record Line(String key, List<Object> arguments) {

        public Line {
            arguments = List.copyOf(arguments);
        }

        public Object[] array() {
            return arguments.toArray();
        }
    }

    private static Line line(String key, Object... arguments) {
        return new Line(key, Arrays.asList(arguments));
    }

    /** The heading, then a line for each directory searched and one for the repository. */
    public static List<Line> of(Backends.Absent absent, Central.Failure failure) {
        List<Line> lines = new ArrayList<>();
        lines.add(line("cli.backend.unavailable", absent.target(), absent.southerVersion()));
        for (Backends.Searched searched : absent.searched()) {
            lines.add(searched(absent.target(), searched));
        }
        lines.add(repository(failure));
        if (failure instanceof Central.Failure.NotAsked
                || failure instanceof Central.Failure.Unreachable) {
            lines.add(line("cli.backend.fetch.later", absent.target()));
        }
        return lines;
    }

    private static Line searched(String target, Backends.Searched searched) {
        return switch (searched) {
            case Backends.Searched.NotThere there ->
                    line("cli.backend.searched.absent", there.directory());
            case Backends.Searched.OtherTargets others -> others.targets().isEmpty()
                    ? line("cli.backend.searched.empty", others.directory())
                    : line("cli.backend.searched.targets", others.directory(),
                            String.join(", ", others.targets()));
            case Backends.Searched.OtherVersions versions ->
                    line("cli.backend.searched.versions", versions.directory(), target,
                            String.join(", ", versions.versions()));
        };
    }

    /** What the repository answered, as the line that says it. */
    public static Line repository(Central.Failure failure) {
        return switch (failure) {
            case Central.Failure.NotAsked _ -> line("cli.backend.central.notasked");
            case Central.Failure.Unregistered unregistered ->
                    line("cli.backend.central.unregistered", unregistered.target());
            case Central.Failure.Unpublished unpublished ->
                    line("cli.backend.central.unpublished", unpublished.target(),
                            unpublished.metadata());
            case Central.Failure.NoneBuilt none ->
                    line("cli.backend.central.none", none.southerVersion(),
                            String.join(", ", none.releases()));
            case Central.Failure.Unreachable unreachable ->
                    line("cli.backend.central.unreachable", unreachable.uri(),
                            unreachable.reason());
            case Central.Failure.Answered answered ->
                    line("cli.backend.central.status", answered.uri(),
                            String.valueOf(answered.status()));
            case Central.Failure.Unreadable unreadable ->
                    line("cli.backend.central.unreadable", unreadable.uri(),
                            unreadable.reason());
            case Central.Failure.NotTheBackend not ->
                    line("cli.backend.central.notthebackend", not.uri(), not.target(),
                            not.southerVersion());
            case Central.Failure.Misconfigured misconfigured ->
                    line("cli.backend.central.misconfigured", misconfigured.setting(),
                            misconfigured.value());
        };
    }
}
