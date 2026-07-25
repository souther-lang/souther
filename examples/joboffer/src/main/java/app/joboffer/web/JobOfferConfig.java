package app.joboffer.web;

import example.joboffer.応募期限を検査する;
import example.joboffer.想定総額;

import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;

import java.time.Clock;

/**
 * Souther 生成物と Spring の配線。どちらの behavior も注入依存を持たない純粋な behavior なので、
 * {@code bind} ではなく {@code of()} で足りる（member / ordering の注入ありパイプラインとの対比）。
 *
 * <p>時計だけは外の世界なので Bean にして境界に置く。ドメインは「今日」を引数で受け取るだけで、
 * 自分で現在時刻を読まない。
 */
@Configuration(proxyBeanMethods = false)
public class JobOfferConfig {

    @Bean
    public 想定総額 想定総額() {
        return 想定総額.of();
    }

    @Bean
    public 応募期限を検査する 応募期限検査() {
        return 応募期限を検査する.of();
    }

    @Bean
    public Clock clock() {
        return Clock.systemDefaultZone();
    }
}
