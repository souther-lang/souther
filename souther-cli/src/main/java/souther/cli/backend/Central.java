package souther.cli.backend;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

import javax.xml.XMLConstants;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.net.URI;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.nio.file.Path;
import java.time.Duration;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * The backends released to a {@link Repository}, and which release of a target's was built against
 * a given Souther.
 *
 * <p>A release says the Souther it was built against as its pom's {@code souther.version}, written
 * there or in a parent pom it names. Every release of the target is a candidate, and the newest of
 * those built against the Souther asked for is the answer: which release is the newest is a matter of
 * the backend's own numbering and says nothing about which Souther it is for, so the repository's
 * {@code latest} and {@code release} are not read. A snapshot is not a release and is not a
 * candidate.
 *
 * <p>What is served is trusted as it is served. A released file on Central does not change, and a
 * backend is released after the Souther it is built against, so nothing about it can be known to
 * this Souther in advance: there is no checksum or key to hold it to. What is held is the way it is
 * reached, which {@link Repository#admits} decides.
 *
 * <p>What the repository serves is read as data and never put into a path as written: a version or
 * a parent's coordinates become a {@link Coordinate} first, and an address is built from those
 * alone. Which target is which artifact is written here, because the artifacts are not named by one
 * rule, so a target this table does not have can still be installed by hand and cannot be fetched;
 * a {@link Release} exists only for a target the table has.
 */
public final class Central implements BackendFetch.Source {

    private static final Coordinate GROUP = new Coordinate("org.souther-lang");

    /** How many releases' poms are asked for at once. */
    private static final int WINDOW = 8;

    /** How many times one request is followed where it is sent on. */
    private static final int REDIRECTS = 5;

    private static final Set<Integer> REDIRECTING = Set.of(301, 302, 303, 307, 308);

    /**
     * A part of a Maven coordinate — a group, an artifact, a version, a classifier — as a path may
     * be built from it: letters, digits, dots, dashes and underscores, starting with a letter or a
     * digit. Nothing a path or an address reads otherwise can be one.
     */
    record Coordinate(String value) {

        Coordinate {
            if (!valid(value)) {
                throw new IllegalArgumentException("not a coordinate: " + value);
            }
        }

        /** The coordinate {@code value} is, where it is one. */
        static Optional<Coordinate> read(String value) {
            return valid(value) ? Optional.of(new Coordinate(value)) : Optional.empty();
        }

        private static boolean valid(String value) {
            return value != null && !value.isEmpty() && Character.isLetterOrDigit(value.charAt(0))
                    && value.chars().allMatch(c -> c < 128 && (Character.isLetterOrDigit(c)
                            || c == '.' || c == '-' || c == '_'));
        }

        @Override
        public String toString() {
            return value;
        }
    }

    /** A target's backend as the repository holds it. */
    record Artifact(Coordinate artifactId, Coordinate classifier) {}

    private static final Map<String, Artifact> ARTIFACTS = Map.of(
            "wasm", new Artifact(new Coordinate("souther-wasm-compiler"), new Coordinate("cli")),
            "native", new Artifact(new Coordinate("souther-native-compiler"),
                    new Coordinate("backend")));

    /**
     * How long the repository is waited for. A metadata file or a pom is small, and has
     * {@code answer} to arrive whole, redirects and all. A jar takes as long as the connection
     * needs: its answer has {@code answer} to begin, and from then on it is ended only where nothing
     * more arrives for {@code stall}.
     */
    record Patience(Duration answer, Duration stall) {
        static final Patience USUAL = new Patience(Duration.ofSeconds(60), Duration.ofSeconds(30));
    }

    /** What the repository answers for one target and one Souther. */
    public sealed interface Answer permits Release, Failure {}

    /** The release to fetch, and where its jar is. Only a target the table has has one. */
    public record Release(String target, String artifactId, String version, URI jar)
            implements Answer {

        public Release {
            if (!ARTIFACTS.containsKey(target)) {
                throw new IllegalArgumentException("no artifact is known for " + target);
            }
        }
    }

    /**
     * Why nothing was fetched, in one of three families: the repository was not asked, it could not
     * be read, or it was read and holds no backend for the pair. Which family a failure is in is
     * what decides what is done with it, so it is the failure's type and not a reading of it.
     */
    public sealed interface Failure extends Answer permits Failure.Unasked, Failure.Unanswered,
            Failure.Declined {

        /** Nothing was asked of the repository. */
        sealed interface Unasked extends Failure permits NotAsked, Unregistered, Misconfigured {}

        /**
         * The repository could not be read: asking it again, later or from elsewhere, may answer.
         * What one release's pom says is not one of these: that is one release's answer.
         */
        sealed interface Unanswered extends Failure
                permits Unreachable, Answered, Unreadable, Redirected {}

        /** The repository was read, and holds no backend for the pair. */
        sealed interface Declined extends Failure permits Unpublished, NoneBuilt, NotTheBackend {}

        /** The repository was not asked, because the run was told to fetch nothing. */
        record NotAsked() implements Unasked {}

        /** No artifact is known for the target, so there is nothing to ask for. */
        record Unregistered(String target) implements Unasked {}

        /** A setting this reads names nothing it can use. */
        record Misconfigured(String setting, String value) implements Unasked {}

        /** Asking for {@code uri} did not get an answer. */
        record Unreachable(URI uri, String reason) implements Unanswered {}

        /** {@code uri} was answered with a status that is not the file. */
        record Answered(URI uri, int status) implements Unanswered {}

        /** What {@code uri} served is not what a repository serves there. */
        record Unreadable(URI uri, String reason) implements Unanswered {}

        /** Asking for {@code uri} was sent on to {@code reached}, which may not be asked. */
        record Redirected(URI uri, URI reached) implements Unanswered {}

        /** The repository has no release of the target's artifact at all. */
        record Unpublished(String target, URI metadata) implements Declined {}

        /**
         * The target is released, and none of {@code releases} is built against the Souther.
         * {@code unstated} are the releases among them whose pom did not say what they were built
         * against, and {@code notVersions} what the metadata lists that is not a version at all:
         * two different things the repository got wrong, kept apart so each is said as what it is.
         */
        record NoneBuilt(String southerVersion, List<String> releases, List<String> unstated,
                         List<String> notVersions) implements Declined {

            public NoneBuilt {
                releases = List.copyOf(releases);
                unstated = List.copyOf(unstated);
                notVersions = List.copyOf(notVersions);
            }
        }

        /** The jar at {@code uri} does not say it is the backend it was released as. */
        record NotTheBackend(URI uri, String target, String southerVersion) implements Declined {}
    }

    /** The repository could not be read, carried out of the steps that ask it. */
    static final class Stop extends Exception {

        private static final long serialVersionUID = 1L;

        private final transient Failure.Unanswered failure;

        Stop(Failure.Unanswered failure) {
            super(failure.toString());
            this.failure = failure;
        }

        Failure.Unanswered failure() {
            return failure;
        }
    }

    /** What one release's pom says it was built against. */
    private sealed interface Stated {
        record Built(String southerVersion) implements Stated {}

        /** The pom, or a parent it names, is missing or says nothing that can be read. */
        record Unstated() implements Stated {}
    }

    private final Repository repository;
    private final Patience patience;

    private Central(Repository repository, Patience patience) {
        this.repository = repository;
        this.patience = patience;
    }

    /**
     * Where this run's settings say to ask, waited for as long as a run usually is. Reading the
     * settings asks nothing, so this is what a run that is told to ask nothing names too.
     */
    public static BackendFetch.Source configured(Map<String, String> environment) {
        return switch (Repository.configured(environment)) {
            case Repository repository -> new Central(repository, Patience.USUAL);
            case Configured.Unusable unusable -> unusable;
        };
    }

    /** The repository at {@code root}, reached directly and waited for as {@code patience} says. */
    static Central at(URI root, Patience patience) {
        return new Central(Repository.at(root), patience);
    }

    @Override
    public String name() {
        return repository.name();
    }

    /**
     * Why {@code target} cannot be asked about, where no artifact is known for it. Answered without
     * asking anything, and so before anything that would be done to ask.
     */
    Optional<Failure.Unregistered> unregistered(String target) {
        return ARTIFACTS.containsKey(target) ? Optional.empty()
                : Optional.of(new Failure.Unregistered(target));
    }

    /** The newest release of {@code target} built against {@code southerVersion}, or why none is. */
    public Answer release(String target, String southerVersion) throws InterruptedException {
        Artifact artifact = ARTIFACTS.get(target);
        if (artifact == null) {
            return new Failure.Unregistered(target);
        }
        URI metadata = artifactRoot(GROUP, artifact.artifactId()).resolve("maven-metadata.xml");
        try {
            HttpResponse<byte[]> listed = small(metadata);
            if (listed.statusCode() == 404) {
                return new Failure.Unpublished(target, metadata);
            }
            List<Coordinate> releases = new ArrayList<>();
            List<String> notVersions = new ArrayList<>();
            for (String listedVersion : texts(child(parse(metadata, served(metadata, listed)),
                    "versioning", "versions"), "version")) {
                Optional<Coordinate> version = Coordinate.read(listedVersion);
                if (version.isEmpty()) {
                    notVersions.add(listedVersion);
                } else if (!listedVersion.endsWith("-SNAPSHOT")) {
                    releases.add(version.get());
                }
            }
            if (releases.isEmpty() && notVersions.isEmpty()) {
                return new Failure.Unpublished(target, metadata);
            }
            releases.sort(Comparator.comparing(Coordinate::value, RELEASE_ORDER));
            List<String> unstated = new ArrayList<>();
            Optional<Coordinate> built = newestBuiltAgainst(artifact, releases.reversed(),
                    southerVersion, unstated);
            if (built.isEmpty()) {
                return new Failure.NoneBuilt(southerVersion,
                        releases.stream().map(Coordinate::value).toList(), unstated, notVersions);
            }
            return new Release(target, artifact.artifactId().value(), built.get().value(),
                    file(GROUP, artifact.artifactId(), built.get(), artifact.classifier(),
                            "jar"));
        } catch (Stop stop) {
            return stop.failure();
        }
    }

    /**
     * The first of {@code newestFirst} whose pom says it was built against {@code southerVersion},
     * where one does. A release whose pom does not say is added to {@code unstated} and passed
     * over: it is one release's answer, and says nothing about the others. A repository that cannot
     * be read ends the search, since the next pom would be asked of the same repository.
     *
     * <p>Each answer is a round trip, two where the Souther is in a parent pom, and a Souther a few
     * releases behind the backend's newest would wait for each in turn. So the poms are asked for
     * {@value #WINDOW} at a time and their answers read in order, newest first: the release taken,
     * and the failure said where one is, are the ones asking one at a time would come to.
     */
    private Optional<Coordinate> newestBuiltAgainst(Artifact artifact,
                                                    List<Coordinate> newestFirst,
                                                    String southerVersion, List<String> unstated)
            throws Stop, InterruptedException {
        try (ExecutorService asking = Executors.newVirtualThreadPerTaskExecutor()) {
            try {
                for (int from = 0; from < newestFirst.size(); from += WINDOW) {
                    List<Coordinate> window = newestFirst.subList(from,
                            Math.min(from + WINDOW, newestFirst.size()));
                    List<Future<Stated>> stated = new ArrayList<>();
                    for (Coordinate version : window) {
                        URI pom = file(GROUP, artifact.artifactId(), version, null, "pom");
                        stated.add(asking.submit(() -> builtAgainst(pom)));
                    }
                    for (int i = 0; i < window.size(); i++) {
                        switch (answer(stated.get(i))) {
                            case Stated.Built built -> {
                                if (built.southerVersion().equals(southerVersion)) {
                                    return Optional.of(window.get(i));
                                }
                            }
                            case Stated.Unstated _ -> unstated.add(window.get(i).value());
                        }
                    }
                }
                return Optional.empty();
            } finally {
                // What is still being asked once the answer is known is ended, not waited for.
                asking.shutdownNow();
            }
        }
    }

    private static Stated answer(Future<Stated> stated) throws Stop, InterruptedException {
        try {
            return stated.get();
        } catch (ExecutionException e) {
            if (e.getCause() instanceof Stop stop) {
                throw stop;
            }
            if (e.getCause() instanceof InterruptedException interrupted) {
                throw interrupted;
            }
            throw new IllegalStateException(e.getCause());
        }
    }

    /**
     * What the pom at {@code pom} says it was built against, read from it or from the parent it
     * names, and from that one's parent, until one says it. A pom, or a parent, that is not there or
     * says nothing that can be read is the release's answer; only a repository that cannot be read
     * stops.
     */
    private Stated builtAgainst(URI pom) throws Stop, InterruptedException {
        Set<URI> read = new HashSet<>();
        URI at = pom;
        while (read.add(at)) {
            HttpResponse<byte[]> answer = small(at);
            if (answer.statusCode() == 404) {
                return new Stated.Unstated();
            }
            Optional<Element> project = parsed(served(at, answer));
            if (project.isEmpty()) {
                return new Stated.Unstated();
            }
            Element stated = child(project.get(), "properties", "souther.version");
            if (stated != null) {
                // Compared as written, as a descriptor's is; an expression Maven left unevaluated
                // in a released pom states nothing, and is not a Souther version that differs.
                String version = stated.getTextContent().strip();
                return Backends.bare(version) && !version.contains("${")
                        ? new Stated.Built(version) : new Stated.Unstated();
            }
            Element parent = child(project.get(), "parent");
            if (parent == null) {
                return new Stated.Unstated();
            }
            Optional<Coordinate> group = Coordinate.read(text(parent, "groupId"));
            Optional<Coordinate> artifactId = Coordinate.read(text(parent, "artifactId"));
            Optional<Coordinate> version = Coordinate.read(text(parent, "version"));
            if (group.isEmpty() || artifactId.isEmpty() || version.isEmpty()) {
                return new Stated.Unstated();
            }
            at = file(group.get(), artifactId.get(), version.get(), null, "pom");
        }
        return new Stated.Unstated();
    }

    /**
     * Writes the release's jar to {@code to}, which is replaced, waiting as {@link Patience} says
     * a jar is waited for.
     */
    void download(Release release, Path to) throws Stop, InterruptedException {
        long deadline = System.nanoTime() + patience.answer().toNanos();
        HttpResponse<Path> done = following(release.jar(), at -> downloadOnce(at, to, deadline));
        if (done.statusCode() != 200) {
            throw new Stop(new Failure.Answered(release.jar(), done.statusCode()));
        }
    }

    /**
     * One request for a jar. It is sent with no timeout of its own, since the client's timeout
     * runs until the body has been read whole and a jar has no time it must arrive in. The answer
     * has until {@code deadline} to begin, and the body is then ended only where the file it is
     * written to has not grown for {@link Patience#stall}, measured from the last time it did.
     */
    private HttpResponse<Path> downloadOnce(URI at, Path to, long deadline)
            throws Stop, InterruptedException {
        AtomicBoolean began = new AtomicBoolean();
        CompletableFuture<HttpResponse<Path>> answer = repository.client().sendAsync(
                HttpRequest.newBuilder(at).GET().build(), begun -> {
                    began.set(true);
                    return HttpResponse.BodySubscribers.ofFile(to);
                });
        long stall = patience.stall().toNanos();
        // Looked at five times a stall, so a download that stopped is ended within a fifth of a
        // stall of the stall it was given, and not up to a stall late.
        long tick = Math.max(1, Math.min(patience.stall().toMillis() / 5, 1000));
        long grew = -1;
        long had = 0;
        try {
            while (true) {
                try {
                    return answer.get(tick, TimeUnit.MILLISECONDS);
                } catch (ExecutionException e) {
                    throw new Stop(new Failure.Unreachable(at, reason(e.getCause())));
                } catch (TimeoutException e) {
                    long now = System.nanoTime();
                    if (!began.get()) {
                        if (now - deadline >= 0) {
                            throw new Stop(new Failure.Unreachable(at, "no answer began in "
                                    + patience.answer().toSeconds() + "s"));
                        }
                        continue;
                    }
                    long has = to.toFile().length();
                    if (grew < 0 || has > had) {
                        grew = now;
                        had = has;
                    } else if (now - grew >= stall) {
                        throw new Stop(new Failure.Unreachable(at,
                                "nothing arrived for " + patience.stall().toSeconds() + "s"));
                    }
                }
            }
        } finally {
            answer.cancel(true);
        }
    }

    /**
     * The answer for a small file: the metadata or a pom, which has {@link Patience#answer} to
     * arrive whole, the redirects it is sent through included.
     */
    private HttpResponse<byte[]> small(URI uri) throws Stop, InterruptedException {
        long deadline = System.nanoTime() + patience.answer().toNanos();
        return following(uri, at -> smallOnce(at, deadline));
    }

    private HttpResponse<byte[]> smallOnce(URI at, long deadline)
            throws Stop, InterruptedException {
        long left = deadline - System.nanoTime();
        if (left <= 0) {
            throw new Stop(new Failure.Unreachable(at,
                    "it did not arrive in " + patience.answer().toSeconds() + "s"));
        }
        // The client's timeout runs until the body is read whole, which is the wait wanted here.
        HttpRequest request = HttpRequest.newBuilder(at).timeout(Duration.ofNanos(left)).GET()
                .build();
        CompletableFuture<HttpResponse<byte[]>> answer =
                repository.client().sendAsync(request, HttpResponse.BodyHandlers.ofByteArray());
        try {
            return answer.get();
        } catch (ExecutionException e) {
            throw new Stop(new Failure.Unreachable(at, reason(e.getCause())));
        } finally {
            answer.cancel(true);
        }
    }

    /** One request, with what is waited for and how. */
    @FunctionalInterface
    private interface Exchange<T> {
        HttpResponse<T> at(URI uri) throws Stop, InterruptedException;
    }

    /**
     * The answer for {@code uri}, following where a redirect sends it, each address held to
     * {@link Repository#admits} before anything is asked of it.
     */
    private static <T> HttpResponse<T> following(URI uri, Exchange<T> exchange)
            throws Stop, InterruptedException {
        URI at = uri;
        for (int hops = 0; hops <= REDIRECTS; hops++) {
            HttpResponse<T> answer = exchange.at(at);
            Optional<String> location = answer.headers().firstValue("Location");
            if (!REDIRECTING.contains(answer.statusCode()) || location.isEmpty()) {
                return answer;
            }
            URI next;
            try {
                next = at.resolve(location.get());
            } catch (IllegalArgumentException e) {
                throw new Stop(new Failure.Unreadable(at,
                        "it sends the request on to `" + location.get() + "`"));
            }
            if (!Repository.admits(next)) {
                throw new Stop(new Failure.Redirected(uri, next));
            }
            at = next;
        }
        throw new Stop(new Failure.Unreadable(uri,
                "it was sent on more than " + REDIRECTS + " times"));
    }

    private static byte[] served(URI uri, HttpResponse<byte[]> answer) throws Stop {
        if (answer.statusCode() != 200) {
            throw new Stop(new Failure.Answered(uri, answer.statusCode()));
        }
        return answer.body();
    }

    private static String reason(Throwable e) {
        return e.getMessage() == null ? e.getClass().getSimpleName() : e.getMessage();
    }

    private URI artifactRoot(Coordinate group, Coordinate artifactId) {
        return repository.root().resolve(group.value().replace('.', '/') + "/" + artifactId + "/");
    }

    private URI file(Coordinate group, Coordinate artifactId, Coordinate version,
                     Coordinate classifier, String extension) {
        String name = artifactId + "-" + version + (classifier == null ? "" : "-" + classifier)
                + "." + extension;
        return artifactRoot(group, artifactId).resolve(version + "/" + name);
    }

    /** The metadata's root element, or a stop that says the repository served something else. */
    private static Element parse(URI uri, byte[] served) throws Stop {
        try {
            return document(served);
        } catch (SAXException | IOException e) {
            throw new Stop(new Failure.Unreadable(uri, e.getMessage()));
        }
    }

    /** A pom's root element, where what was served is a document. */
    private static Optional<Element> parsed(byte[] served) {
        try {
            return Optional.of(document(served));
        } catch (SAXException | IOException e) {
            return Optional.empty();
        }
    }

    /**
     * The document's root element. Read with no DTD and no external entity, since a repository's
     * metadata and poms have neither and a document that declares one is not one of them.
     */
    private static Element document(byte[] served) throws SAXException, IOException {
        try {
            DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
            factory.setFeature(XMLConstants.FEATURE_SECURE_PROCESSING, true);
            factory.setFeature("http://apache.org/xml/features/disallow-doctype-decl", true);
            factory.setXIncludeAware(false);
            factory.setExpandEntityReferences(false);
            DocumentBuilder builder = factory.newDocumentBuilder();
            // The default handler writes a fatal error to standard error as well as throwing it,
            // and what is said about it here is the failure the run reports.
            builder.setErrorHandler(new DefaultHandler());
            Document document = builder.parse(new ByteArrayInputStream(served));
            return document.getDocumentElement();
        } catch (ParserConfigurationException e) {
            throw new IllegalStateException(e);
        }
    }

    /** The element reached from {@code from} by the names, each a child of the last, or null. */
    private static Element child(Element from, String... names) {
        Element at = from;
        for (String name : names) {
            if (at == null) {
                return null;
            }
            Element next = null;
            for (Node node = at.getFirstChild(); node != null; node = node.getNextSibling()) {
                if (node instanceof Element element && element.getTagName().equals(name)) {
                    next = element;
                    break;
                }
            }
            at = next;
        }
        return at;
    }

    private static String text(Element from, String name) {
        Element element = child(from, name);
        return element == null ? null : element.getTextContent().strip();
    }

    private static List<String> texts(Element from, String name) {
        List<String> found = new ArrayList<>();
        if (from == null) {
            return found;
        }
        for (Node node = from.getFirstChild(); node != null; node = node.getNextSibling()) {
            if (node instanceof Element element && element.getTagName().equals(name)) {
                found.add(element.getTextContent().strip());
            }
        }
        return found;
    }

    /**
     * Which of two releases is newer, by their numbering.
     *
     * <p>A version is read as a run of parts, split at dots and dashes and wherever digits meet
     * letters, so {@code 0.1.0-rc3} is {@code 0 1 0 rc 3}. Numbers compare as numbers, and a missing
     * number as zero. A word is older than a number or than the end of the version, so a release
     * candidate comes before its release, and words compare as text.
     */
    static final Comparator<String> RELEASE_ORDER = Central::compareReleases;

    private static int compareReleases(String left, String right) {
        List<String> a = parts(left);
        List<String> b = parts(right);
        for (int i = 0; i < Math.max(a.size(), b.size()); i++) {
            String x = i < a.size() ? a.get(i) : null;
            String y = i < b.size() ? b.get(i) : null;
            int order = compareParts(x, y);
            if (order != 0) {
                return order;
            }
        }
        return left.compareTo(right);
    }

    private static int compareParts(String x, String y) {
        boolean xNumber = x == null || number(x);
        boolean yNumber = y == null || number(y);
        if (xNumber && yNumber) {
            String m = x == null ? "0" : strip(x);
            String n = y == null ? "0" : strip(y);
            return m.length() != n.length() ? Integer.compare(m.length(), n.length())
                    : m.compareTo(n);
        }
        if (xNumber) {
            return 1;
        }
        if (yNumber) {
            return -1;
        }
        return x.compareToIgnoreCase(y);
    }

    private static boolean number(String part) {
        return part.chars().allMatch(Character::isDigit);
    }

    private static String strip(String digits) {
        int start = 0;
        while (start < digits.length() - 1 && digits.charAt(start) == '0') {
            start++;
        }
        return digits.substring(start);
    }

    private static List<String> parts(String version) {
        List<String> parts = new ArrayList<>();
        StringBuilder part = new StringBuilder();
        for (int i = 0; i < version.length(); i++) {
            char c = version.charAt(i);
            if (c == '.' || c == '-') {
                parts.add(part.toString());
                part.setLength(0);
                continue;
            }
            if (!part.isEmpty() && Character.isDigit(c) != Character.isDigit(part.charAt(0))) {
                parts.add(part.toString());
                part.setLength(0);
            }
            part.append(c);
        }
        parts.add(part.toString());
        return parts;
    }
}
