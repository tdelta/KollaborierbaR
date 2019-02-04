import static org.hamcrest.MatcherAssert.*;
import static org.hamcrest.Matchers.*;
import static org.mockito.Mockito.*;
import static org.springframework.test.web.servlet.request.MockMvcRequestBuilders.*;
import static org.springframework.test.web.servlet.result.MockMvcResultMatchers.*;

import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import org.junit.runner.RunWith;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.autoconfigure.web.servlet.WebMvcTest;
import org.springframework.http.MediaType;
import org.springframework.test.context.ContextConfiguration;
import org.springframework.test.context.junit4.SpringRunner;
import org.springframework.test.web.servlet.MockMvc;
import server.Application;
import server.ProjectController;

@RunWith(SpringRunner.class)
@ContextConfiguration(classes = Application.class)
@WebMvcTest(ProjectController.class)
public class ProjectApiTest {

  @Autowired private MockMvc mvc;

  @Rule public TemporaryFolder tmpFolder = new TemporaryFolder();

  @Before
  public void createTestProject() throws Exception {
    mvc.perform(put("/projects/TestProject"));
  }

  @Test
  public void testGetProjects() throws Exception {
    mvc.perform(put("/projects/TestProject"));
    mvc.perform(get("/projects"))
        .andExpect(status().isOk())
        .andExpect(content().contentTypeCompatibleWith(MediaType.APPLICATION_JSON))
        .andExpect(content().json("[\"HelloWorld\",\"JMLProject\",\"My Project\"]"));
    // .andExpect(jsonPath("$[0]", is("HelloWorld")));
  }
}
