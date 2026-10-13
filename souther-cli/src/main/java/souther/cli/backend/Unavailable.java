package souther.cli.backend;

import java.net.URI;
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

    /** A line, with every address in it shown as {@link Shown} shows one. */
    private static Line line(String key, Object... arguments) {
        return new Line(key, Arrays.stream(arguments)
                .map(argument -> argument instanceof URI uri ? Shown.address(uri) : argument)
                .toList());
    }

    /**
     * The heading, then a line for each directory searched and one for the repository, which is
     * called {@code repository} there.
     */
    public static List<Line> of(Backends.Absent absent, Central.Failure failure,
                                String repository) {
        List<Line> lines = new ArrayList<>();
        lines.add(line("cli.backend.unavailable", absent.target(), absent.southerVersion()));
        for (Backends.Searched searched : absent.searched()) {
            lines.add(searched(absent.target(), searched));
        }
        lines.addAll(repository(failure, repository));
        if (askingLaterMayAnswer(failure)) {
            lines.add(line("cli.backend.fetch.later", absent.target()));
        }
        return lines;
    }

    /**
     * Whether fetching ahead of the compile, where the repository can be reached, may answer what
     * this run could not: where the run was told to ask nothing, or the repository could not be
     * read. Where nothing can be asked about the target, or the repository was read and holds no
     * backend for the pair, asking again answers the same.
     */
    private static boolean askingLaterMayAnswer(Central.Failure failure) {
        return switch (failure) {
            case Central.Failure.Unasked unasked -> unasked instanceof Central.Failure.NotAsked;
            case Central.Failure.Unanswered _ -> true;
            case Central.Failure.Declined _, Central.Failure.Unkept _ -> false;
        };
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

    /**
     * What the repository, called {@code repository}, answered, as the lines that say it: one,
     * and where no release was built against the Souther, one more for each thing the repository
     * served that could not be read.
     */
    public static List<Line> repository(Central.Failure failure, String repository) {
        if (!(failure instanceof Central.Failure.NoneBuilt none)) {
            return List.of(answered(failure, repository));
        }
        List<Line> lines = new ArrayList<>();
        lines.add(answered(failure, repository));
        if (!none.unstated().isEmpty()) {
            lines.add(line("cli.backend.central.unstated", repository,
                    String.join(", ", none.unstated())));
        }
        if (!none.notVersions().isEmpty()) {
            // Said, and not repeated: it is served text that did not read as a version.
            lines.add(line("cli.backend.central.notversions", repository));
        }
        return lines;
    }

    private static Line answered(Central.Failure failure, String repository) {
        return switch (failure) {
            case Central.Failure.NotAsked _ -> line("cli.backend.central.notasked", repository);
            case Central.Failure.Unregistered unregistered ->
                    line("cli.backend.central.unregistered", repository, unregistered.target());
            case Central.Failure.Unpublished unpublished ->
                    line("cli.backend.central.unpublished", repository, unpublished.target(),
                            unpublished.metadata());
            case Central.Failure.NoneBuilt none ->
                    line("cli.backend.central.none", repository, none.southerVersion(),
                            String.join(", ", none.releases()));
            case Central.Failure.Unreachable unreachable ->
                    line("cli.backend.central.unreachable", repository, unreachable.uri(),
                            unreachable.reason());
            case Central.Failure.Answered answered ->
                    line("cli.backend.central.status", repository, answered.uri(),
                            String.valueOf(answered.status()));
            case Central.Failure.Unreadable unreadable ->
                    line("cli.backend.central.unreadable", repository, unreadable.uri(),
                            unreadable.reason());
            case Central.Failure.Redirected redirected ->
                    line("cli.backend.central.redirected", repository, redirected.uri(),
                            redirected.reached());
            case Central.Failure.NotTheBackend not ->
                    line("cli.backend.central.notthebackend", repository, not.uri(),
                            not.target(), not.southerVersion());
            case Central.Failure.Misconfigured misconfigured -> switch (misconfigured.why()) {
                case Central.Failure.Misread.NotAnAddress _ ->
                        line("cli.backend.central.misconfigured", repository,
                                misconfigured.setting());
                case Central.Failure.Misread.Credentials credentials ->
                        line("cli.backend.central.misconfigured.credentials", repository,
                                misconfigured.setting(), credentials.named());
                case Central.Failure.Misread.Insecure insecure ->
                        line("cli.backend.central.misconfigured.insecure", repository,
                                misconfigured.setting(), insecure.named());
                case Central.Failure.Misread.Scheme scheme ->
                        line("cli.backend.central.misconfigured.scheme", repository,
                                misconfigured.setting(), scheme.named());
            };
            case Central.Failure.Unwritable unwritable ->
                    line("cli.backend.unwritable", unwritable.directory(), unwritable.reason());
        };
    }
}
