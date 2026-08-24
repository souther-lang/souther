package souther.test;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

/**
 * The files this repository holds, as git has them.
 *
 * <p>{@link RepositoryLayout} answers where sources are kept; this answers what the repository
 * owns. They are different questions and a check needs one or the other. What the formatter sweeps
 * is sources, so it asks the layout. What a check about the repository's prose sweeps — a citation
 * written in an ADR, a heading quoted in a document — is not source and lives nowhere near a
 * {@code src}, so it asks this.
 *
 * <p>Asking git rather than the filesystem settles what a build wrote in one place, and it is a
 * place the repository already keeps honest: {@code target/} and {@code .surefire-*} are in
 * {@code .gitignore} because that is where a build's output is declared. A walk of the working tree
 * would have to name them again, and name whatever is written next as well.
 *
 * <p>The index and not the working tree, so this is what has been committed or staged. A file
 * nobody has added yet is a file the repository does not hold: a scratch directory somebody keeps
 * beside the modules is theirs, and a repository-wide check whose answer changed because of it
 * would be reporting on that machine rather than on this repository.
 *
 * <p>No git means no answer, and this refuses rather than returning an empty list or standing
 * aside. The question is whether an invariant holds over the files the repository owns; without git
 * that set is unobserved, which is not the same as its being empty. Nothing in
 * {@link RepositoryLayout} needs git, so a check that only reads sources still runs where there is
 * no work tree.
 */
public final class GitIndex {

    private final Path root;
    private final List<Path> tracked;

    private GitIndex(Path root, List<Path> tracked) {
        this.root = root;
        this.tracked = List.copyOf(tracked);
    }

    /** What git holds in {@code layout}'s repository. */
    public static GitIndex of(RepositoryLayout layout) {
        Path root = layout.root();
        List<Path> tracked = new ArrayList<>();
        for (String name : run(root, "ls-files", "-z", "--cached").split("\0")) {
            if (!name.isEmpty()) {
                tracked.add(Path.of(name));
            }
        }
        if (tracked.isEmpty()) {
            throw new IllegalStateException("git holds no file under " + root
                    + ": this reads the repository's own files and there are none to read");
        }
        tracked.sort(Path::compareTo);
        return new GitIndex(root, tracked);
    }

    /**
     * Every file git holds, relative to the repository root, sorted.
     *
     * <p>Relative because that is the identity git gives a file, and the same identity a check
     * writes in an expected value. {@link #resolve} turns one into somewhere to read.
     */
    public List<Path> trackedFiles() {
        return tracked;
    }

    /** Every {@code .sou} git holds. */
    public List<Path> trackedSoutherSources() {
        return tracked.stream()
                .filter(each -> each.getFileName().toString().endsWith(".sou"))
                .toList();
    }

    /** Where to read one of them. */
    public Path resolve(Path tracked) {
        return root.resolve(tracked);
    }

    private static String run(Path root, String... arguments) {
        List<String> command = new ArrayList<>(List.of("git", "-C", root.toString()));
        command.addAll(List.of(arguments));
        Path complaint;
        Process git;
        try {
            // What git says about itself goes to a file rather than a pipe. Read from a pipe it
            // would have to be read while the list is being read, and one reader cannot do both:
            // git blocked writing a full stderr pipe never finishes writing the list this is
            // blocked reading.
            complaint = Files.createTempFile("git-ls-files", ".err");
            git = new ProcessBuilder(command)
                    .redirectError(ProcessBuilder.Redirect.to(complaint.toFile()))
                    .start();
        } catch (IOException noGit) {
            throw new IllegalStateException("cannot run " + String.join(" ", command)
                    + ": this reads what the repository holds and git is what holds it", noGit);
        }
        byte[] out;
        String err;
        int status;
        try {
            out = git.getInputStream().readAllBytes();
            if (!git.waitFor(2, TimeUnit.MINUTES)) {
                git.destroyForcibly();
                throw new IllegalStateException(String.join(" ", command) + " did not finish");
            }
            status = git.exitValue();
            err = Files.readString(complaint, StandardCharsets.UTF_8).trim();
        } catch (IOException unreadable) {
            throw new UncheckedIOException(unreadable);
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            throw new IllegalStateException(String.join(" ", command) + " was interrupted",
                    interrupted);
        } finally {
            try {
                Files.deleteIfExists(complaint);
            } catch (IOException leftBehind) {
                throw new UncheckedIOException(leftBehind);
            }
        }
        if (status != 0) {
            throw new IllegalStateException(String.join(" ", command) + " exited " + status + ": "
                    + err);
        }
        return new String(out, StandardCharsets.UTF_8);
    }
}
