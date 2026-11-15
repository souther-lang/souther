package souther.cli.backend;

import com.sun.net.httpserver.HttpExchange;
import com.sun.net.httpserver.HttpServer;

import java.io.IOException;
import java.io.OutputStream;
import java.net.InetAddress;
import java.net.InetSocketAddress;
import java.net.URI;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.Executors;

/**
 * A Maven repository in Central's layout, served over HTTP on the loopback address for the length of
 * a test, which says every path it was asked for.
 *
 * <p>A path is served in one way, which {@link Serving} names, and is held back for a while first
 * where the test says so: what is served and when it begins are the two things a test varies, and
 * each path has one of each.
 */
public final class LocalRepository implements AutoCloseable {

    private static final String ROOT = "/maven2/";
    private static final String GROUP = "org/souther-lang/";

    /** How a path is answered. */
    private sealed interface Serving {

        /** The file, whole, or a 404 where there is none. */
        record Whole() implements Serving {}

        /** This status, and nothing else. */
        record Status(int status) implements Serving {}

        /** The request sent on to {@code location}, with a body of {@code length} bytes. */
        record Redirect(String location, int length) implements Serving {}

    }

    private final HttpServer server;
    private final Map<String, byte[]> files = new ConcurrentHashMap<>();
    private final Map<String, Serving> serving = new ConcurrentHashMap<>();
    private final List<String> asked = new CopyOnWriteArrayList<>();

    /** Guards the poms held for one another: their width, how many are left to answer, how many
     *  are waiting now, and the groups already let go. */
    private final Object pomGate = new Object();
    private int pomWidth;
    private int pomsUnanswered;
    private int pomsWaiting;
    private int pomGroups;
    private boolean closed;
    private final List<Integer> pomsLetGoTogether = new ArrayList<>();

    private LocalRepository(HttpServer server) {
        this.server = server;
    }

    public static LocalRepository start() throws IOException {
        HttpServer server = HttpServer.create(
                new InetSocketAddress(InetAddress.getLoopbackAddress(), 0), 0);
        LocalRepository repository = new LocalRepository(server);
        server.createContext("/", repository::serve);
        // A thread for each exchange, as a real repository answers requests at once.
        server.setExecutor(Executors.newVirtualThreadPerTaskExecutor());
        server.start();
        return repository;
    }

    /** Where the repository is, as {@code souther.repository} names it. */
    public URI uri() {
        return URI.create("http://127.0.0.1:" + server.getAddress().getPort() + ROOT);
    }

    /** Every path asked for, in the order asked. */
    public List<String> asked() {
        return List.copyOf(asked);
    }

    /** Lists {@code versions} as the artifact's. */
    public void metadata(String artifactId, String... versions) {
        StringBuilder listed = new StringBuilder();
        for (String version : versions) {
            listed.append("      <version>").append(version).append("</version>\n");
        }
        put(GROUP + artifactId + "/maven-metadata.xml", """
                <?xml version="1.0" encoding="UTF-8"?>
                <metadata>
                  <groupId>org.souther-lang</groupId>
                  <artifactId>%s</artifactId>
                  <versioning>
                    <latest>%s</latest>
                    <versions>
                %s    </versions>
                  </versioning>
                </metadata>
                """.formatted(artifactId, versions.length == 0 ? "" : versions[versions.length - 1],
                listed));
    }

    /** A pom stating the Souther it was built against. */
    public static String builtAgainst(String artifactId, String version, String southerVersion) {
        return """
                <project xmlns="http://maven.apache.org/POM/4.0.0">
                  <modelVersion>4.0.0</modelVersion>
                  <groupId>org.souther-lang</groupId>
                  <artifactId>%s</artifactId>
                  <version>%s</version>
                  <properties>
                    <souther.version>%s</souther.version>
                  </properties>
                </project>
                """.formatted(artifactId, version, southerVersion);
    }

    /** A pom stating no Souther, and naming a parent. */
    public static String inheriting(String artifactId, String version, String parentId,
                                    String parentVersion) {
        return """
                <project xmlns="http://maven.apache.org/POM/4.0.0">
                  <modelVersion>4.0.0</modelVersion>
                  <parent>
                    <groupId>org.souther-lang</groupId>
                    <artifactId>%s</artifactId>
                    <version>%s</version>
                  </parent>
                  <artifactId>%s</artifactId>
                  <properties>
                    <jackson.version>3.0.0</jackson.version>
                  </properties>
                </project>
                """.formatted(parentId, parentVersion, artifactId);
    }

    /** Serves {@code pom} as the release's pom. */
    public void pom(String artifactId, String version, String pom) {
        put(path(artifactId, version, null, "pom"), pom);
    }

    /** Serves the jar at {@code jar} as the release's jar under {@code classifier}. */
    public void jar(String artifactId, String version, String classifier, Path jar)
            throws IOException {
        files.put(path(artifactId, version, classifier, "jar"), Files.readAllBytes(jar));
    }

    /** Serves a release: its pom built against {@code southerVersion}, and its jar. */
    public void release(String artifactId, String version, String classifier,
                        String southerVersion, Path jar) throws IOException {
        pom(artifactId, version, builtAgainst(artifactId, version, southerVersion));
        jar(artifactId, version, classifier, jar);
    }

    /** Answers the release's jar with {@code status} and nothing else. */
    public void answer(String artifactId, String version, String classifier, int status) {
        serving.put(path(artifactId, version, classifier, "jar"), new Serving.Status(status));
    }

    /** Answers {@code path} by sending the request on to {@code location}. */
    public void redirect(String path, String location) {
        redirect(path, location, 0);
    }

    /** As {@link #redirect(String, String)}, with a body of {@code length} bytes as well. */
    public void redirect(String path, String location, int length) {
        serving.put(path, new Serving.Redirect(location, length));
    }

    /**
     * Begins the answer for no pom until as many are waiting as there are to ask for in a group:
     * {@code width}, or the poms still unanswered where that is fewer, out of {@code poms} in all.
     * A repository far away leaves a client that asks one at a time waiting for each, and such a
     * client never has a group waiting, so its first pom is never answered. A test that holds poms
     * is bounded by its own timeout.
     */
    public void holdPomsInGroupsOf(int width, int poms) {
        synchronized (pomGate) {
            pomWidth = width;
            pomsUnanswered = poms;
        }
    }

    /** How many poms were waiting together each time the poms held by {@link #holdPomsInGroupsOf}
     *  were let go, in the order they were. */
    public List<Integer> pomsLetGoTogether() {
        synchronized (pomGate) {
            return List.copyOf(pomsLetGoTogether);
        }
    }

    private void holdPom() throws InterruptedException {
        synchronized (pomGate) {
            if (pomWidth == 0) {
                return;
            }
            int mine = pomGroups;
            pomsWaiting++;
            if (pomsWaiting >= Math.min(pomWidth, pomsUnanswered)) {
                pomsLetGoTogether.add(pomsWaiting);
                pomsUnanswered -= pomsWaiting;
                pomsWaiting = 0;
                pomGroups++;
                pomGate.notifyAll();
            }
            while (pomGroups == mine && !closed) {
                pomGate.wait();
            }
        }
    }

    public void put(String path, String content) {
        files.put(path, content.getBytes(StandardCharsets.UTF_8));
    }

    public static String path(String artifactId, String version, String classifier,
                              String extension) {
        return GROUP + artifactId + "/" + version + "/" + artifactId + "-" + version
                + (classifier == null ? "" : "-" + classifier) + "." + extension;
    }

    private void serve(HttpExchange exchange) throws IOException {
        String path = exchange.getRequestURI().getPath();
        asked.add(path);
        String file = path.startsWith(ROOT) ? path.substring(ROOT.length()) : path;
        if (file.endsWith(".pom")) {
            try {
                holdPom();
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
        }
        byte[] content = files.get(file);
        try (exchange) {
            switch (serving.getOrDefault(file, new Serving.Whole())) {
                case Serving.Status status -> exchange.sendResponseHeaders(status.status(), -1);
                case Serving.Redirect redirect -> {
                    exchange.getResponseHeaders().add("Location", redirect.location());
                    if (redirect.length() == 0) {
                        exchange.sendResponseHeaders(302, -1);
                    } else {
                        exchange.sendResponseHeaders(302, redirect.length());
                        try (OutputStream body = exchange.getResponseBody()) {
                            body.write(new byte[redirect.length()]);
                        }
                    }
                }
                case Serving.Whole _ -> {
                    if (content == null) {
                        exchange.sendResponseHeaders(404, -1);
                    } else {
                        exchange.sendResponseHeaders(200, content.length);
                        try (OutputStream body = exchange.getResponseBody()) {
                            body.write(content);
                        }
                    }
                }
            }
        }
    }

    @Override
    public void close() {
        synchronized (pomGate) {
            closed = true;
            pomGate.notifyAll();
        }
        server.stop(0);
    }
}
