package souther.cli.init;

import souther.compiler.Reserved;
import souther.compiler.diag.Messages;
import souther.compiler.text.DisplayColumns;
import souther.compiler.meta.ModuleMetadata;

import java.io.IOException;
import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

/**
 * {@code souther init}: starts a project, or adds Souther to one that exists.
 *
 * <p>What it decides is settled before anything is written. Where the project goes, what it is
 * called, which build runs it and how much of a model it starts with are read off the line and off
 * the directory, and only then is a file created — so what this reports and what it wrote are one
 * answer rather than two walks that agree.
 *
 * <p>Nothing already there is overwritten, and what was left alone is reported. Re-running is how a
 * half-finished project is finished, and a command that silently wrote over a model somebody had
 * begun would make the second run the expensive one.
 *
 * <p>Never interactive. The binary this command belongs to answers questions so that neither a
 * person nor a coding agent has to hunt through a workspace, and a prompt is a question only one of
 * those two can answer.
 */
public final class InitCommand {

    private InitCommand() {}

    public static int run(String[] args, Locale locale, PrintStream out, PrintStream err) {
        return run(args, locale, out, err, Path.of("."), ModuleMetadata.releasedVersion());
    }

    /**
     * As above, from a directory and a version the caller states.
     *
     * <p>Both are the run's own facts rather than the process's, so that a test drives this command
     * the way a shell does: in a directory of its own, and as a release that has a version. A
     * compiler running from class files has no manifest and no version to write into a build file,
     * which is a refusal here and not a placeholder somebody has to find later.
     */
    static int run(String[] args, Locale locale, PrintStream out, PrintStream err, Path here,
                   String souther) {
        String coordinateAsWritten = null;
        Path directory = null;
        String buildAsWritten = null;
        String modelAsWritten = null;
        String moduleAsWritten = null;
        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
                case "-d", "--dir" -> directory = Path.of(args[++i]);
                case "--build" -> buildAsWritten = args[++i];
                case "--model" -> modelAsWritten = args[++i];
                case "--module" -> moduleAsWritten = args[++i];
                default -> {
                    if (coordinateAsWritten != null) {
                        return refuse(err, locale, "cli.init.arguments",
                                coordinateAsWritten + ", " + args[i]);
                    }
                    coordinateAsWritten = args[i];
                }
            }
        }

        BuildSystem asked = buildAsWritten == null ? null : BuildSystem.written(buildAsWritten);
        if (buildAsWritten != null && asked == null) {
            return refuse(err, locale, "cli.option.values", "--build",
                    String.join(", ", BuildSystem.spellings()), buildAsWritten);
        }
        Model level = modelAsWritten == null ? null : Model.written(modelAsWritten);
        if (modelAsWritten != null && level == null) {
            return refuse(err, locale, "cli.option.values", "--model",
                    String.join(", ", Model.spellings()), modelAsWritten);
        }
        if (souther == null) {
            return refuse(err, locale, "cli.init.version");
        }

        Path at = directory != null ? directory : here;
        BuildSystem existing = Files.isDirectory(at) ? BuildSystem.of(at) : null;
        List<Line> report = new ArrayList<>();
        Coordinate coordinate;
        Path target;
        if (existing != null) {
            // A build that is already there decides three of the four: which build runs this, what
            // the project is called, and that what is being added is a model rather than a project.
            if (asked != null) {
                return refuse(err, locale, "cli.init.build.decided", existing.spelling());
            }
            if (coordinateAsWritten != null) {
                return refuse(err, locale, "cli.init.coordinate.declared", coordinateAsWritten);
            }
            coordinate = coordinateOf(existing, at);
            if (coordinate == null) {
                return refuse(err, locale, "cli.init.coordinate.unreadable",
                        display(here, existing.fileIn(at)), Coordinate.FORM);
            }
            target = at;
            if (level == null) {
                level = Model.NONE;
            }
            report.add(new Line(Did.DETECTED, existing.spelling() + " ("
                    + existing.fileIn(at).getFileName() + ")"));
            report.add(new Line(Did.READ, coordinate.toString()));
        } else {
            if (coordinateAsWritten == null) {
                return refuse(err, locale, "cli.init.coordinate.required", Coordinate.FORM);
            }
            coordinate = Coordinate.written(coordinateAsWritten);
            if (coordinate == null) {
                return refuse(err, locale, "cli.init.coordinate.form", coordinateAsWritten,
                        Coordinate.FORM);
            }
            target = directory != null ? directory : here.resolve(coordinate.artifactId());
            if (asked == null) {
                asked = BuildSystem.MAVEN;
            }
            if (level == null) {
                level = Model.FULL;
            }
        }

        String module = moduleAsWritten != null ? moduleAsWritten : coordinate.moduleName();
        if (module == null) {
            return refuse(err, locale, "cli.init.module.underivable", coordinate.toString());
        }
        if (!Coordinate.isAModuleName(module)) {
            return refuse(err, locale, "cli.init.module.name", module);
        }
        if (Reserved.isNamespace(module)) {
            return refuse(err, locale, "cli.init.module.reserved", module);
        }

        Project project = new Project(coordinate, module, level,
                existing != null ? existing : asked, souther);
        try {
            for (Templates.File file : filesOf(project, existing == null)) {
                Line line = write(target.resolve(file.path()), file.content(), here);
                List<Note> notes = notesUnder(file.path(), project, module);
                report.add(notes.isEmpty() ? line
                        : new Line(line.verb(), line.subject(), notes));
            }
            if (existing != null) {
                report.add(edit(existing, at, project, here));
            }
        } catch (IOException e) {
            say(out, report, locale);
            err.println(Messages.get("cli.init.io", locale, e.getMessage()));
            return 1;
        }
        say(out, report, locale);
        out.println();
        next(out, project, target, here, locale);
        return 0;
    }

    /**
     * What this project starts with: the sources always, and the build's own files where the project
     * is being created.
     *
     * <p>The build file comes first because it is what a reader opens first, and what follows it is
     * what it compiles.
     */
    private static List<Templates.File> filesOf(Project project, boolean creating) {
        List<Templates.File> files = new ArrayList<>();
        if (creating) {
            if (project.build() == BuildSystem.MAVEN) {
                files.add(new Templates.File("pom.xml", Templates.pom(project)));
            } else {
                files.add(new Templates.File("settings.gradle.kts",
                        Templates.settingsScript(project)));
                files.add(new Templates.File("build.gradle.kts", Templates.buildScript(project)));
            }
            files.add(new Templates.File(".gitignore", Templates.gitignore(project)));
        }
        files.addAll(Templates.sourcesOf(project));
        return files;
    }

    /**
     * What is worth saying under a file this command just wrote.
     *
     * <p>The module name, under the file whose header it is. It is the one name here that was
     * derived rather than written down by the author, and it is also the Java package their own
     * code imports from, so it is said where they can see it. Everything else these files say, they
     * say themselves.
     */
    private static List<Note> notesUnder(String path, Project project, String module) {
        return path.equals(Templates.modelPathOf(project))
                ? List.of(new Note("cli.init.module", module))
                : List.of();
    }

    /** What the build that is already here calls the project, or null where it does not say. */
    private static Coordinate coordinateOf(BuildSystem build, Path at) {
        try {
            Path file = build.fileIn(at);
            String text = Files.readString(file);
            if (build == BuildSystem.MAVEN) {
                return MavenBuild.coordinateOf(text);
            }
            String group = GradleBuild.groupOf(text);
            if (group == null) {
                return null;
            }
            // Gradle's own rule for a project that names none: the directory it is in. Read rather
            // than guessed at — this is the name the build itself would use.
            String name = null;
            for (String settings : List.of("settings.gradle.kts", "settings.gradle")) {
                Path path = at.resolve(settings);
                if (Files.isRegularFile(path)) {
                    name = GradleBuild.rootProjectNameOf(Files.readString(path));
                }
            }
            if (name == null) {
                Path absolute = at.toAbsolutePath().normalize();
                name = absolute.getFileName() == null ? null : absolute.getFileName().toString();
            }
            return name == null ? null : new Coordinate(group, name);
        } catch (IOException e) {
            return null;
        }
    }

    /**
     * Writes one file, or leaves the one that is there.
     *
     * <p>What is already written is never opened. A model somebody has begun is the reason to run
     * this command again, and reading it to decide whether it is worth keeping would be this command
     * having an opinion about their model.
     */
    private static Line write(Path file, String content, Path here) throws IOException {
        if (Files.exists(file)) {
            return new Line(Did.KEPT, display(here, file));
        }
        Path parent = file.getParent();
        if (parent != null) {
            Files.createDirectories(parent);
        }
        Files.writeString(file, content);
        return new Line(Did.CREATED, display(here, file));
    }

    /**
     * Puts the declaration into a build that exists, or reports that it is already there.
     *
     * <p>Whether anything was added is decided by what the text came back as, and not by asking a
     * second time. A pom declaring the plugin and not the runtime is missing one of the two, and a
     * check that answered "already declared" to it would leave a build that stops with the plugin's
     * own refusal.
     */
    private static Line edit(BuildSystem build, Path at, Project project, Path here)
            throws IOException {
        Path file = build.fileIn(at);
        String was = Files.readString(file);
        String now = build == BuildSystem.MAVEN
                ? MavenBuild.withSoutherDeclared(was, project.southerVersion())
                : GradleBuild.declaresThePlugin(was) ? was
                        : GradleBuild.withThePluginApplied(was,
                                GradleBuild.isKotlin(file.getFileName().toString()));
        if (now.equals(was)) {
            return new Line(Did.KEPT, display(here, file));
        }
        List<Note> notes = new ArrayList<>();
        if (Backups.areNeededFor(file)) {
            Path backup = file.resolveSibling(file.getFileName() + ".orig");
            Files.writeString(backup, was);
            notes.add(new Note("cli.init.orig", display(here, backup)));
        }
        Files.writeString(file, now);
        return new Line(Did.EDITED, display(here, file), notes);
    }

    /** What to run next, which is the one thing a reader does after this command. */
    private static void next(PrintStream out, Project project, Path target, Path here,
                             Locale locale) {
        String where = display(here, target);
        String cd = where.isEmpty() || where.equals(".") ? "" : "cd " + where + " && ";
        if (project.build() == BuildSystem.MAVEN) {
            out.println("    " + cd + "mvn test");
            return;
        }
        // A wrapper is not written here — one written at release time pins a Gradle version this
        // command has no way of revisiting — so a project that has none is told how to make one.
        boolean wrapper = Files.isRegularFile(target.resolve("gradlew"));
        out.println("    " + cd + (wrapper ? "./gradlew test" : "gradle wrapper && ./gradlew test"));
        if (!wrapper && !onThePath("gradle")) {
            out.println();
            out.println("    " + Messages.get("cli.init.gradle", locale));
        }
    }

    /** Whether a command of this name is on the PATH this process was started with. */
    private static boolean onThePath(String command) {
        String path = System.getenv("PATH");
        if (path == null) {
            return false;
        }
        for (String entry : path.split(java.io.File.pathSeparator)) {
            if (!entry.isBlank() && Files.isExecutable(Path.of(entry).resolve(command))) {
                return true;
            }
        }
        return false;
    }

    /**
     * What this command did to one thing.
     *
     * <p>Each with the key it is written under, spelt out. A key built by joining a stem to a name
     * is a key no reader of this source can find and no check over the catalog can see, which is how
     * a message comes to be defined and shown by nothing.
     */
    private enum Did {
        DETECTED("cli.init.verb.detected"),
        READ("cli.init.verb.read"),
        CREATED("cli.init.verb.created"),
        KEPT("cli.init.verb.kept"),
        EDITED("cli.init.verb.edited");

        private final String key;

        Did(String key) {
            this.key = key;
        }
    }

    /** One line of what this command did: what it did, to what, and what else is worth saying. */
    private record Line(Did verb, String subject, List<Note> notes) {

        Line(Did verb, String subject) {
            this(verb, subject, List.of());
        }
    }

    /** Something worth saying under a line, in the language the run answers in. */
    private record Note(String key, Object said) {}

    /**
     * Writes what was done, one line per file, with the verbs in a column.
     *
     * <p>Both the created and the kept files. A run that reported only what it wrote reads as though
     * the rest of the project were not there, which is exactly the question somebody re-running this
     * command is asking.
     */
    private static void say(PrintStream out, List<Line> lines, Locale locale) {
        // In columns and not in characters. `created` and `\u4f5c\u6210` are seven characters and two, and
        // four columns and four; padded by length the Japanese run puts every subject and every
        // note somewhere else than the English one does.
        int column = 0;
        for (Line line : lines) {
            column = Math.max(column, DisplayColumns.width(verb(line, locale)));
        }
        for (Line line : lines) {
            String verb = verb(line, locale);
            out.println(INDENT + DisplayColumns.padRight(verb, column + GAP) + line.subject());
            for (Note note : line.notes()) {
                out.println(INDENT + " ".repeat(column + GAP)
                        + Messages.get(note.key(), locale, note.said()));
            }
        }
    }

    /** What every line this command writes begins with. */
    private static final String INDENT = "    ";

    /** What stands between the widest verb and what is written against it. */
    private static final int GAP = 2;

    private static String verb(Line line, Locale locale) {
        return Messages.get(line.verb().key, locale);
    }

    /** How a path is named in front of a reader: relative to where they ran this, where it is. */
    private static String display(Path here, Path file) {
        Path from = here.toAbsolutePath().normalize();
        Path to = file.toAbsolutePath().normalize();
        if (to.startsWith(from)) {
            String relative = from.relativize(to).toString();
            return relative.isEmpty() ? "." : relative;
        }
        return file.toString();
    }

    private static int refuse(PrintStream err, Locale locale, String key, Object... args) {
        err.println(Messages.get(key, locale, args));
        return 2;
    }
}
