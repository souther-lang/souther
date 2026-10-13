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
import java.net.InetSocketAddress;
import java.net.ProxySelector;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.nio.file.Path;
import java.time.Duration;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
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
 * The backends released to a Maven repository, Maven Central unless {@code souther.repository}
 * names another, and which release of a target's was built against a given Souther.
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
 * reached, which is HTTPS, or plain HTTP to this machine's own loopback address only.
 *
 * <p>Which target is which artifact is written here, because the artifacts are not named by one
 * rule. A target this table does not have can still be installed by hand; it cannot be fetched.
 */
public final class Central {

    /** Where releases are fetched from unless {@code souther.repository} says otherwise. */
    public static final URI MAVEN_CENTRAL = URI.create("https://repo.maven.apache.org/maven2/");

    private static final String GROUP = "org.souther-lang";

    private static final String REPOSITORY = "souther.repository";

    private static final Duration CONNECT = Duration.ofSeconds(15);
    private static final Duration ANSWER = Duration.ofSeconds(60);
    private static final Duration STALL = Duration.ofSeconds(30);

    /** How many releases' poms are asked for at once. */
    private static final int WINDOW = 8;

    /** How many times one request is followed where it is sent on. */
    private static final int REDIRECTS = 5;

    private static final Set<Integer> REDIRECTING = Set.of(301, 302, 303, 307, 308);

    private static final Set<String> LOOPBACK = Set.of("localhost", "127.0.0.1", "[::1]");

    /** A target's backend as the repository holds it. */
    record Artifact(String artifactId, String classifier) {}

    private static final Map<String, Artifact> ARTIFACTS = Map.of(
            "wasm", new Artifact("souther-wasm-compiler", "cli"),
            "native", new Artifact("souther-native-compiler", "backend"));

    /** What the repository answers for one target and one Souther. */
    public sealed interface Answer permits Release, Failure {}

    /** The release to fetch, and where its jar is. */
    public record Release(String target, String artifactId, String version, URI jar)
            implements Answer {}

    /** Why nothing was fetched, as far as the repository is concerned. */
    public sealed interface Failure extends Answer {

        /** The repository was not asked, because the run was told to fetch nothing. */
        record NotAsked() implements Failure {}

        /** No artifact is known for the target, so there is nothing to ask for. */
        record Unregistered(String target) implements Failure {}

        /** The repository has no release of the target's artifact at all. */
        record Unpublished(String target, URI metadata) implements Failure {}

        /**
         * The target is released, and none of {@code releases} is built against the Souther.
         * {@code unreadable} are the releases among them, or listed beside them, whose pom could
         * not be read for the Souther it was built against.
         */
        record NoneBuilt(String southerVersion, List<String> releases, List<String> unreadable)
                implements Failure {

            public NoneBuilt {
                releases = List.copyOf(releases);
                unreadable = List.copyOf(unreadable);
            }
        }

        /** Asking for {@code uri} did not get an answer. */
        record Unreachable(URI uri, String reason) implements Failure {}

        /** {@code uri} was answered with a status that is not the file. */
        record Answered(URI uri, int status) implements Failure {}

        /** What {@code uri} served is not what a repository serves there. */
        record Unreadable(URI uri, String reason) implements Failure {}

        /** Asking for {@code uri} was sent on to {@code reached}, which is not reached securely. */
        record Redirected(URI uri, URI reached) implements Failure {}

        /** The jar at {@code uri} does not say it is the backend it was released as. */
        record NotTheBackend(URI uri, String target, String southerVersion) implements Failure {}

        /** A setting this reads names nothing it can use. */
        record Misconfigured(String setting, String value) implements Failure {}
    }

    /** A failure carried out of the steps that ask, to the one that answers. */
    static final class Stop extends Exception {

        private static final long serialVersionUID = 1L;

        private final transient Failure failure;

        Stop(Failure failure) {
            super(failure.toString());
            this.failure = failure;
        }

        Failure failure() {
            return failure;
        }
    }

    private final URI repository;
    private final HttpClient client;
    private final Failure misconfigured;

    /** How long a download may go with nothing arriving before it is taken to have stopped. */
    private final Duration stall;

    private Central(URI repository, HttpClient client, Failure misconfigured, Duration stall) {
        this.repository = repository;
        this.client = client;
        this.misconfigured = misconfigured;
        this.stall = stall;
    }

    private Central(URI repository, HttpClient client, Failure misconfigured) {
        this(repository, client, misconfigured, STALL);
    }

    /**
     * The repository this run fetches from, reached through the proxy it is told to use.
     *
     * <p>The proxy is Java's {@code https.proxyHost} where that is set, and otherwise the one
     * {@code HTTPS_PROXY} names, which is how a proxy is told to every other tool on the machine.
     * A repository on this machine's loopback address, or on a host {@code NO_PROXY} names, is
     * reached directly. A setting that cannot be
     * read is not passed over: every question is answered with what it was set to.
     */
    public static Central configured(Map<String, String> environment) {
        String named = System.getProperty(REPOSITORY);
        URI repository = MAVEN_CENTRAL;
        if (named != null && !named.isBlank()) {
            repository = repository(named);
            if (repository == null) {
                return new Central(MAVEN_CENTRAL, null,
                        new Failure.Misconfigured(REPOSITORY, named));
            }
        }
        HttpClient.Builder builder = client();
        if (loopback(repository) || bypassed(repository.getHost(), either(environment,
                "NO_PROXY", "no_proxy"))) {
            builder.proxy(HttpClient.Builder.NO_PROXY);
        } else if (System.getProperty("https.proxyHost") == null) {
            String proxy = either(environment, "HTTPS_PROXY", "https_proxy");
            if (proxy != null) {
                InetSocketAddress address = proxyAddress(proxy);
                if (address == null) {
                    return new Central(repository, null,
                            new Failure.Misconfigured("HTTPS_PROXY", proxy));
                }
                builder.proxy(ProxySelector.of(address));
            }
        }
        return new Central(repository, builder.build(), null);
    }

    /**
     * What the repository is called where it is named to a reader: Maven Central, or the address
     * {@code souther.repository} gives in its place, since a reader told Central answered would look
     * for the fault somewhere it is not.
     */
    public static String named() {
        String named = System.getProperty(REPOSITORY);
        return named == null || named.isBlank() ? "Maven Central" : named;
    }

    /** The first of the two spellings a variable is set under that is not blank, or null. */
    private static String either(Map<String, String> environment, String upper, String lower) {
        for (String name : List.of(upper, lower)) {
            String value = environment.get(name);
            if (value != null && !value.isBlank()) {
                return value.strip();
            }
        }
        return null;
    }

    /**
     * Whether {@code NO_PROXY} names the host: a list split at commas, each a host, a domain that
     * covers its subdomains with or without a leading dot, or {@code *} for every host.
     */
    static boolean bypassed(String host, String noProxy) {
        if (host == null || noProxy == null) {
            return false;
        }
        String asked = host.toLowerCase(Locale.ROOT);
        for (String entry : noProxy.split(",")) {
            String named = entry.strip().toLowerCase(Locale.ROOT);
            String domain = named.startsWith(".") ? named.substring(1) : named;
            if (named.equals("*") || (!domain.isEmpty()
                    && (asked.equals(domain) || asked.endsWith("." + domain)))) {
                return true;
            }
        }
        return false;
    }

    /**
     * The repository at {@code repository}, reached with no proxy, where a download that has had
     * nothing for {@code stall} has stopped.
     */
    static Central at(URI repository, Duration stall) {
        return new Central(repository, client().proxy(HttpClient.Builder.NO_PROXY).build(), null,
                stall);
    }

    /** A client that follows no redirect itself: {@link #following} does, and holds where to. */
    private static HttpClient.Builder client() {
        return HttpClient.newBuilder().connectTimeout(CONNECT)
                .followRedirects(HttpClient.Redirect.NEVER);
    }

    /** The repository a setting names, or null where it names none that may be fetched from. */
    private static URI repository(String named) {
        URI uri;
        try {
            uri = new URI(named.endsWith("/") ? named : named + "/");
        } catch (URISyntaxException e) {
            return null;
        }
        if (!uri.isAbsolute() || uri.getHost() == null) {
            return null;
        }
        return secure(uri) ? uri : null;
    }

    /** Whether the host is this machine's loopback, as a name or an address, asking no resolver. */
    private static boolean loopback(URI uri) {
        String host = uri.getHost();
        return host != null && LOOPBACK.contains(host.toLowerCase(Locale.ROOT));
    }

    /** Where {@code HTTPS_PROXY} says the proxy is, written as a URL or as host and port. */
    private static InetSocketAddress proxyAddress(String proxy) {
        URI uri;
        try {
            uri = new URI(proxy.contains("://") ? proxy : "http://" + proxy);
        } catch (URISyntaxException e) {
            return null;
        }
        if (uri.getHost() == null) {
            return null;
        }
        int port = uri.getPort() >= 0 ? uri.getPort() : "https".equals(uri.getScheme()) ? 443 : 80;
        return InetSocketAddress.createUnresolved(uri.getHost(), port);
    }

    /**
     * Why {@code target} cannot be asked about at all, or null where it can: no artifact is known
     * for it, or a setting names nothing to ask. Answered without asking anything.
     */
    public Failure unaskable(String target) {
        if (misconfigured != null) {
            return misconfigured;
        }
        return ARTIFACTS.containsKey(target) ? null : new Failure.Unregistered(target);
    }

    /** The newest release of {@code target} built against {@code southerVersion}, or why none is. */
    public Answer release(String target, String southerVersion) throws InterruptedException {
        Failure unasked = unaskable(target);
        if (unasked != null) {
            return unasked;
        }
        Artifact artifact = ARTIFACTS.get(target);
        try {
            URI metadata = artifactRoot(GROUP, artifact.artifactId()).resolve("maven-metadata.xml");
            HttpResponse<byte[]> listed = ask(metadata);
            if (listed.statusCode() == 404) {
                return new Failure.Unpublished(target, metadata);
            }
            List<String> releases = new ArrayList<>();
            List<String> unreadable = new ArrayList<>();
            for (String version : texts(child(parse(metadata, served(metadata, listed)),
                    "versioning", "versions"), "version")) {
                if (!coordinate(version)) {
                    unreadable.add(version);
                } else if (!version.endsWith("-SNAPSHOT")) {
                    releases.add(version);
                }
            }
            if (releases.isEmpty() && unreadable.isEmpty()) {
                return new Failure.Unpublished(target, metadata);
            }
            releases.sort(RELEASE_ORDER);
            String built = newestBuiltAgainst(artifact, releases.reversed(), southerVersion,
                    unreadable);
            return built == null ? new Failure.NoneBuilt(southerVersion, releases, unreadable)
                    : new Release(target, artifact.artifactId(), built,
                            file(GROUP, artifact.artifactId(), built, artifact.classifier(),
                                    "jar"));
        } catch (Stop stop) {
            return stop.failure();
        }
    }

    /**
     * Whether a version, group or artifact read from the repository is one a path can be built
     * from: what Maven coordinates are written in, and nothing a path or a URI reads otherwise.
     */
    private static boolean coordinate(String value) {
        return !value.isEmpty() && Character.isLetterOrDigit(value.charAt(0))
                && value.chars().allMatch(c -> c < 128 && (Character.isLetterOrDigit(c)
                        || c == '.' || c == '-' || c == '_'));
    }

    /**
     * The first of {@code newestFirst} whose pom says it was built against {@code southerVersion},
     * or null. A release whose pom is not there or says nothing that can be read is added to
     * {@code unreadable} and passed over: it is one release that cannot be told apart, and says
     * nothing about the others. A repository that cannot be reached, or that answers with an error,
     * ends the search, since it is the same repository the next pom would be asked of.
     *
     * <p>Each answer is a round trip, two where the Souther is in a parent pom, and a Souther a few
     * releases behind the backend's newest would wait for each in turn. So the poms are asked for
     * {@value #WINDOW} at a time and their answers read in order, newest first: the release taken,
     * and the failure said where one is, are the ones asking one at a time would come to.
     */
    private String newestBuiltAgainst(Artifact artifact, List<String> newestFirst,
                                      String southerVersion, List<String> unreadable)
            throws Stop, InterruptedException {
        try (ExecutorService asking = Executors.newVirtualThreadPerTaskExecutor()) {
            try {
                for (int from = 0; from < newestFirst.size(); from += WINDOW) {
                    List<String> window = newestFirst.subList(from,
                            Math.min(from + WINDOW, newestFirst.size()));
                    List<Future<String>> stated = new ArrayList<>();
                    for (String version : window) {
                        URI pom = file(GROUP, artifact.artifactId(), version, null, "pom");
                        stated.add(asking.submit(() -> builtAgainst(pom)));
                    }
                    for (int i = 0; i < window.size(); i++) {
                        String said = answer(stated.get(i));
                        if (said == null) {
                            unreadable.add(window.get(i));
                        } else if (said.equals(southerVersion)) {
                            return window.get(i);
                        }
                    }
                }
                return null;
            } finally {
                // What is still being asked once the answer is known is ended, not waited for.
                asking.shutdownNow();
            }
        }
    }

    /** What one pom said, or null where it said nothing that can be read. */
    private static String answer(Future<String> stated) throws Stop, InterruptedException {
        try {
            return stated.get();
        } catch (ExecutionException e) {
            if (e.getCause() instanceof Stop stop) {
                boolean missing = stop.failure() instanceof Failure.Answered answered
                        && answered.status() == 404;
                if (missing || stop.failure() instanceof Failure.Unreadable) {
                    return null;
                }
                throw stop;
            }
            if (e.getCause() instanceof InterruptedException interrupted) {
                throw interrupted;
            }
            throw new IllegalStateException(e.getCause());
        }
    }

    /**
     * Writes the release's jar to {@code to}, which is replaced.
     *
     * <p>A jar takes as long as the connection needs, so what ends a download is a connection that
     * stops: one through which nothing more has arrived for {@link #stall}. A request's own timeout
     * ends only the wait for the answer to begin, and a download stopped part way through would
     * otherwise wait for ever.
     */
    void download(Release release, Path to) throws Stop, InterruptedException {
        HttpResponse<Path> done = following(release.jar(), at -> downloadOnce(at, to));
        if (done.statusCode() != 200) {
            throw new Stop(new Failure.Answered(release.jar(), done.statusCode()));
        }
    }

    private HttpResponse<Path> downloadOnce(URI at, Path to) throws Stop, InterruptedException {
        // Until the answer begins, the request's own timeout is what is waited on.
        AtomicBoolean began = new AtomicBoolean();
        CompletableFuture<HttpResponse<Path>> answer = client.sendAsync(request(at), begun -> {
            began.set(true);
            return HttpResponse.BodySubscribers.ofFile(to);
        });
        long had = -1;
        while (true) {
            try {
                return answer.get(stall.toMillis(), TimeUnit.MILLISECONDS);
            } catch (ExecutionException e) {
                throw new Stop(new Failure.Unreachable(at, reason(e.getCause())));
            } catch (TimeoutException e) {
                if (!began.get()) {
                    continue;
                }
                long has = to.toFile().length();
                if (has == had) {
                    answer.cancel(true);
                    throw new Stop(new Failure.Unreachable(at,
                            "nothing arrived for " + stall.toSeconds() + "s"));
                }
                had = has;
            } catch (InterruptedException e) {
                answer.cancel(true);
                throw e;
            }
        }
    }

    /** One request, with what is waited for and how. */
    @FunctionalInterface
    private interface Exchange<T> {
        HttpResponse<T> at(URI uri) throws Stop, InterruptedException;
    }

    /**
     * The answer for {@code uri}, following where a redirect sends it.
     *
     * <p>Followed here rather than by the client, so where a redirect points is held to what a
     * repository is reached over — HTTPS, or plain HTTP on the loopback address — before anything is
     * asked of it. The client's own following refuses only HTTPS to plain HTTP, and would take a
     * repository on the loopback address to plain HTTP anywhere.
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
            if (!secure(next)) {
                throw new Stop(new Failure.Redirected(uri, next));
            }
            at = next;
        }
        throw new Stop(new Failure.Unreadable(uri,
                "it was sent on more than " + REDIRECTS + " times"));
    }

    /**
     * The Souther the pom at {@code pom} says it was built against, read from it or from the parent
     * it names, and from that one's parent, until one says it.
     */
    private String builtAgainst(URI pom) throws Stop, InterruptedException {
        Set<URI> read = new HashSet<>();
        URI at = pom;
        while (read.add(at)) {
            HttpResponse<byte[]> answer = ask(at);
            Element project = parse(at, served(at, answer));
            Element stated = child(project, "properties", "souther.version");
            if (stated != null) {
                String version = stated.getTextContent().strip();
                if (!Backends.bare(version) || version.contains("${")) {
                    throw new Stop(new Failure.Unreadable(at,
                            "souther.version is `" + version + "`"));
                }
                return version;
            }
            Element parent = child(project, "parent");
            if (parent == null) {
                throw new Stop(new Failure.Unreadable(pom, "no souther.version is stated"));
            }
            String group = text(parent, "groupId");
            String artifactId = text(parent, "artifactId");
            String version = text(parent, "version");
            if (group == null || artifactId == null || version == null) {
                throw new Stop(new Failure.Unreadable(at, "the parent is not named"));
            }
            if (!coordinate(group) || !coordinate(artifactId) || !coordinate(version)) {
                throw new Stop(new Failure.Unreadable(at, "the parent is named as `" + group
                        + ":" + artifactId + ":" + version + "`"));
            }
            at = file(group, artifactId, version, null, "pom");
        }
        throw new Stop(new Failure.Unreadable(pom, "its parents name each other"));
    }

    /** The answer for a small file, which has {@link #ANSWER} to arrive whole. */
    private HttpResponse<byte[]> ask(URI uri) throws Stop, InterruptedException {
        return following(uri, this::askOnce);
    }

    private HttpResponse<byte[]> askOnce(URI at) throws Stop, InterruptedException {
        CompletableFuture<HttpResponse<byte[]>> answer =
                client.sendAsync(request(at), HttpResponse.BodyHandlers.ofByteArray());
        try {
            return answer.get(ANSWER.toMillis(), TimeUnit.MILLISECONDS);
        } catch (ExecutionException e) {
            throw new Stop(new Failure.Unreachable(at, reason(e.getCause())));
        } catch (TimeoutException e) {
            answer.cancel(true);
            throw new Stop(new Failure.Unreachable(at,
                    "it did not arrive in " + ANSWER.toSeconds() + "s"));
        } catch (InterruptedException e) {
            answer.cancel(true);
            throw e;
        }
    }

    private static boolean secure(URI uri) {
        return "https".equals(uri.getScheme())
                || ("http".equals(uri.getScheme()) && loopback(uri));
    }

    private static byte[] served(URI uri, HttpResponse<byte[]> answer) throws Stop {
        if (answer.statusCode() != 200) {
            throw new Stop(new Failure.Answered(uri, answer.statusCode()));
        }
        return answer.body();
    }

    private static HttpRequest request(URI uri) {
        return HttpRequest.newBuilder(uri).timeout(ANSWER).GET().build();
    }

    private static String reason(Throwable e) {
        return e.getMessage() == null ? e.getClass().getSimpleName() : e.getMessage();
    }

    private URI artifactRoot(String group, String artifactId) {
        return repository.resolve(group.replace('.', '/') + "/" + artifactId + "/");
    }

    private URI file(String group, String artifactId, String version, String classifier,
                     String extension) {
        String name = artifactId + "-" + version + (classifier == null ? "" : "-" + classifier)
                + "." + extension;
        return artifactRoot(group, artifactId).resolve(version + "/" + name);
    }

    /**
     * The document's root element. Read with no DTD and no external entity, since a repository's
     * metadata and poms have neither and a document that declares one is not one of them.
     */
    private static Element parse(URI uri, byte[] served) throws Stop {
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
        } catch (SAXException | IOException e) {
            throw new Stop(new Failure.Unreadable(uri, e.getMessage()));
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
