package server;

import com.intuit.karate.junit4.Karate;
import org.junit.runner.RunWith;
import com.intuit.karate.KarateOptions;

@RunWith(Karate.class)
@KarateOptions(features = "classpath:ProjectLifeCycle.feature")
public class ProjectLifeCycle {
}
