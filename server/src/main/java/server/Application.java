package server;

import com.google.common.base.Predicates;
import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.ComponentScan;
import springfox.documentation.builders.PathSelectors;
import springfox.documentation.builders.RequestHandlerSelectors;
import springfox.documentation.spi.DocumentationType;
import springfox.documentation.spring.web.plugins.Docket;
import springfox.documentation.swagger2.annotations.EnableSwagger2;

@SpringBootApplication
@ComponentScan(basePackages = {"server", "synchronization"})
@EnableSwagger2
public class Application {
  @Bean
  public Docket petApi() {
    return new Docket(DocumentationType.SWAGGER_2)
        .select()
        .apis(Predicates.not(RequestHandlerSelectors.basePackage("org.springframework")))
        .paths(PathSelectors.any())
        .build()
        .pathMapping("/");
  }

  public static void main(String[] args) {
    SpringApplication.run(Application.class, args);
  }
}
