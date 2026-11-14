package souther.cli.backend;

import java.net.URI;
import java.net.http.HttpClient;
import java.net.http.HttpHeaders;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.nio.ByteBuffer;
import java.time.Duration;
import java.util.Collections;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Flow;
import java.util.concurrent.Future;
import java.util.concurrent.TimeoutException;
import java.util.function.Consumer;
import javax.net.ssl.SSLSession;

/**
 * A {@link Central.Wire} whose time passes only where {@link Central} waits, and whose scripted
 * answers happen at the times the script says.
 *
 * <p>A request whose path ends with a scripted suffix is answered by its script, which says when
 * the answer begins, when bytes arrive and when it ends, as a length of time from when the request
 * was sent. Every other request goes to {@code real}. Waiting on a scripted answer runs the events
 * up to the end of the wait and then moves the time there, so what {@link Central} saw at each of
 * its looks, and when it gave up, is read off {@link #elapsed()}.
 */
final class ScriptedWire implements Central.Wire {

    /** One scripted answer, as it is delivered to whatever asked for it. */
    final class Delivery<T> {

        private final HttpResponse.BodyHandler<T> handler;
        private final CompletableFuture<HttpResponse<T>> answer;
        private HttpResponse.BodySubscriber<T> body;

        private Delivery(HttpResponse.BodyHandler<T> handler,
                         CompletableFuture<HttpResponse<T>> answer) {
            this.handler = handler;
            this.answer = answer;
        }

        /** The answer begins, with its body still to come. */
        void begin() {
            body = handler.apply(new Info());
            body.onSubscribe(new Flow.Subscription() {
                @Override
                public void request(long n) {
                }

                @Override
                public void cancel() {
                }
            });
        }

        void bytes(byte[] received) {
            body.onNext(List.of(ByteBuffer.wrap(received)));
        }

        /** The body ends, and the answer with it. */
        void end() {
            body.onComplete();
            answer.complete(new Reply<>(body.getBody().toCompletableFuture().join()));
        }

        /** {@code run} {@code later} after the request was sent. */
        void after(Duration later, Runnable run) {
            events.add(new Event(sentAt + later.toNanos(), order++, run));
        }

        private long sentAt = now;
    }

    private record Event(long at, long order, Runnable run) {}

    private record Info() implements HttpResponse.ResponseInfo {
        @Override
        public int statusCode() {
            return 200;
        }

        @Override
        public HttpHeaders headers() {
            return HttpHeaders.of(Map.of(), (name, value) -> true);
        }

        @Override
        public HttpClient.Version version() {
            return HttpClient.Version.HTTP_1_1;
        }
    }

    private record Reply<T>(T body) implements HttpResponse<T> {
        @Override
        public int statusCode() {
            return 200;
        }

        @Override
        public HttpRequest request() {
            return null;
        }

        @Override
        public Optional<HttpResponse<T>> previousResponse() {
            return Optional.empty();
        }

        @Override
        public HttpHeaders headers() {
            return HttpHeaders.of(Map.of(), (name, value) -> true);
        }

        @Override
        public Optional<SSLSession> sslSession() {
            return Optional.empty();
        }

        @Override
        public URI uri() {
            return null;
        }

        @Override
        public HttpClient.Version version() {
            return HttpClient.Version.HTTP_1_1;
        }
    }

    private final Central.Wire real;
    private final Map<String, Consumer<Delivery<?>>> scripts = new LinkedHashMap<>();
    private final PriorityQueue<Event> events = new PriorityQueue<>(
            Comparator.comparingLong(Event::at).thenComparingLong(Event::order));
    private final Set<Object> scripted = Collections.newSetFromMap(new IdentityHashMap<>());
    private volatile long now;
    private long order;

    ScriptedWire(Central.Wire real) {
        this.real = real;
    }

    /** Answers the requests whose path ends with {@code suffix} as {@code script} says. */
    void script(String suffix, Consumer<Delivery<?>> script) {
        scripts.put(suffix, script);
    }

    /** The time that has passed where {@link Central} waited. */
    Duration elapsed() {
        return Duration.ofNanos(now);
    }

    @Override
    public <T> CompletableFuture<HttpResponse<T>> send(HttpRequest request,
                                                       HttpResponse.BodyHandler<T> body) {
        for (Map.Entry<String, Consumer<Delivery<?>>> script : scripts.entrySet()) {
            if (request.uri().getPath().endsWith(script.getKey())) {
                CompletableFuture<HttpResponse<T>> answer = new CompletableFuture<>();
                scripted.add(answer);
                script.getValue().accept(new Delivery<>(body, answer));
                return answer;
            }
        }
        return real.send(request, body);
    }

    @Override
    public long nanos() {
        return now;
    }

    @Override
    public <T> T get(Future<T> answer, long nanos)
            throws ExecutionException, TimeoutException, InterruptedException {
        if (!scripted.contains(answer)) {
            return real.get(answer, nanos);
        }
        long until = now + nanos;
        while (!answer.isDone() && !events.isEmpty() && events.peek().at() <= until) {
            Event next = events.poll();
            now = Math.max(now, next.at());
            next.run().run();
        }
        if (answer.isDone()) {
            return answer.get();
        }
        now = until;
        throw new TimeoutException();
    }
}
