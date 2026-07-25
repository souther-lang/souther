package app.joboffer;

import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;

/**
 * Spring Boot の起動点。{@code @SpringBootTest} はこのクラスを見つけてコンテキストを起動する。
 * データベースは無いので、autoconfig が用意するのは Web スタックと Jackson だけ。
 */
@SpringBootApplication(proxyBeanMethods = false)
public class JobOfferApplication {
    public static void main(String[] args) {
        SpringApplication.run(JobOfferApplication.class, args);
    }
}
