import org.junit.Before;
import org.junit.Test;
import static org.junit.Assert.assertThat;
import static org.junit.Assert.assertEquals;
import static org.hamcrest.collection.IsIterableContainingInAnyOrder.containsInAnyOrder;

import server.ProjectController;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

/**
 * Class for JUnit tests of Project controller and its dependencies
 */
public class ProjectControllerTest {
    // prepear tests
    ProjectController testProjectController= new ProjectController();
    List<String> testProjects = new LinkedList<String>();
    File testFile = new File("projects/HelloWorld");

    @Before
    public void hallo(){
        testProjects.add("HelloWorld");
        testProjects.add("My Project");
    }

    /**
     * Execute tests!
     */
    @Test
    public void test() {
        // Testing listProjects()
        assertThat(
          "The server contains the default project folders", 
          testProjectController.listProjects(),
          containsInAnyOrder(testProjects.toArray())
        );

        // Testing showProject()
        assertEquals("LICENSE", testProjectController.showProject("HelloWorld").contents.get(0).getName());
        assertEquals("file", testProjectController.showProject("HelloWorld").contents.get(0).gettype());
        assertEquals("src", testProjectController.showProject("HelloWorld").contents.get(1).getName());
        assertEquals("folder", testProjectController.showProject("HelloWorld").contents.get(1).gettype());

        // Testing createFolderItem
        assertEquals("folder", testProjectController.createFolderItem(testFile).gettype());
        assertEquals("HelloWorld", testProjectController.createFolderItem(testFile).getName());
        assertEquals("LICENSE", testProjectController.createFolderItem(testFile).getContents().get(0).getName());

        // Testing selectProjectFromArray
        assertEquals("src", testProjectController.selectProjectFromArray(testFile.listFiles(), "src").getName());
    }
}
