package souther.test;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.time.Duration;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;
import java.util.function.BooleanSupplier;

/**
 * What something in another thread writes, for a test that waits for a particular thing to be
 * written and not for a time to pass.
 *
 * <p>A wait ends when what it waits for is there, or when the writer has said it is done, so how fast
 * the writer is decides nothing. The bound a wait is given is for the writer that never writes: it
 * ends the wait of a test whose writer hung, and no test is wrong for taking long.
 */
public final class WrittenOutput extends OutputStream {

    private final ReentrantLock lock = new ReentrantLock();

    private final Condition changed = lock.newCondition();

    private final ByteArrayOutputStream bytes = new ByteArrayOutputStream();

    private boolean ended;

    @Override
    public void write(int b) {
        lock.lock();
        try {
            bytes.write(b);
            changed.signalAll();
        } finally {
            lock.unlock();
        }
    }

    @Override
    public void write(byte[] b, int off, int len) {
        lock.lock();
        try {
            bytes.write(b, off, len);
            changed.signalAll();
        } finally {
            lock.unlock();
        }
    }

    /** Everything written so far. */
    public byte[] bytes() {
        lock.lock();
        try {
            return bytes.toByteArray();
        } finally {
            lock.unlock();
        }
    }

    /** The writer will write no more, so a wait for what it has not written is over. */
    public void ended() {
        lock.lock();
        try {
            ended = true;
            changed.signalAll();
        } finally {
            lock.unlock();
        }
    }

    /**
     * Waits until {@code written} holds, which it is asked each time something more is written.
     * Whether it was asked of the output as the writer left it: false where the writer ended or
     * {@code hungAfter} passed with it still not holding.
     *
     * @throws InterruptedException where the waiting thread was interrupted
     */
    public boolean awaitUntil(BooleanSupplier written, Duration hungAfter)
            throws InterruptedException {
        lock.lock();
        try {
            long patience = hungAfter.toNanos();
            while (!written.getAsBoolean()) {
                if (ended || patience <= 0) {
                    return false;
                }
                patience = changed.awaitNanos(patience);
            }
            return true;
        } finally {
            lock.unlock();
        }
    }
}
