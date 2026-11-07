package souther.compiler.partition;

import org.junit.jupiter.api.extension.ExtensionContext;
import org.junit.jupiter.api.extension.InvocationInterceptor;
import org.junit.jupiter.api.extension.ReflectiveInvocationContext;

import java.lang.reflect.Method;

/**
 * Runs each test as a compilation holding every figure to the one declared answers
 * ({@link Allowances#DECLARED}): for a test that asks what a compilation's working comes to of
 * that working itself, outside any store, and reaches a figure a compilation may set, which is
 * made only while one answers.
 */
final class AsACompilationHoldingTheDeclaredFiguresAnswers implements InvocationInterceptor {

    @Override
    public void interceptTestMethod(Invocation<Void> invocation,
                                    ReflectiveInvocationContext<Method> invocationContext,
                                    ExtensionContext extensionContext) throws Throwable {
        Throwable[] thrown = new Throwable[1];
        Allowances.DECLARED.over(() -> {
            try {
                invocation.proceed();
            } catch (Throwable each) {
                thrown[0] = each;
            }
            return null;
        });
        if (thrown[0] != null) {
            throw thrown[0];
        }
    }
}
