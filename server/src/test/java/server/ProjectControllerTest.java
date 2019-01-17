import org.junit.Before;
import org.junit.Test;
import static org.junit.Assert.assertThat;
import static org.junit.Assert.assertEquals;
import static org.hamcrest.collection.IsIterableContainingInAnyOrder.containsInAnyOrder;
import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.Matchers.contains;
import static org.hamcrest.Matchers.hasItem;
import static org.hamcrest.Matchers.allOf;
import static org.hamcrest.beans.HasPropertyWithValue.hasProperty;

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
        testProjects.add("JMLProject");
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
        assertThat(
            "Project HelloWorld contains the file LICENSE",
            testProjectController.showProject("HelloWorld").contents,
            hasItem(
                allOf(
                    hasProperty("name", is("LICENSE")),
                    hasProperty("type", is("file")))
            ));

        assertThat(
            "Project HelloWorld contains the folder src",
            testProjectController.showProject("HelloWorld").contents,
            hasItem(
                allOf(
                hasProperty("name", is("src")),
                hasProperty("type", is("folder")))
            ));
        
        // Testing createFolderItem
        assertEquals("folder", testProjectController.createFolderItem(testFile).gettype());
        assertEquals("HelloWorld", testProjectController.createFolderItem(testFile).getName());
        assertThat(
            "Folder Item projects/HelloWorld contains the file LICENSE",
            testProjectController.createFolderItem(testFile).getContents(),
            hasItem(
                hasProperty("name", is("LICENSE"))));

        // Testing selectProjectFromArray
        assertEquals("src", testProjectController.selectProjectFromArray(testFile.listFiles(), "src").getName());
    }
}
