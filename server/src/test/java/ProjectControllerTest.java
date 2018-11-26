import junit.framework.TestCase;
import org.junit.Before;
import org.junit.Test;
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
        TestCase.assertEquals(testProjects, testProjectController.listProjects());

        // Testing showProject()
        TestCase.assertEquals("LICENSE", testProjectController.showProject("HelloWorld").contents.get(0).getName());
        TestCase.assertEquals("file", testProjectController.showProject("HelloWorld").contents.get(0).gettype());
        TestCase.assertEquals("src", testProjectController.showProject("HelloWorld").contents.get(1).getName());
        TestCase.assertEquals("folder", testProjectController.showProject("HelloWorld").contents.get(1).gettype());

        // Testing createFolderItem
        TestCase.assertEquals("folder", testProjectController.createFolderItem(testFile).gettype());
        TestCase.assertEquals("HelloWorld", testProjectController.createFolderItem(testFile).getName());
        TestCase.assertEquals("LICENSE", testProjectController.createFolderItem(testFile).getContents().get(0).getName());

        // Testing selectProjectFromArray
        TestCase.assertEquals("src", testProjectController.selectProjectFromArray(testFile.listFiles(), "src").getName());
    }
}
