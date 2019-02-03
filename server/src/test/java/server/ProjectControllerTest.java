package server;

import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.Matchers.allOf;
import static org.hamcrest.Matchers.hasItem;
import static org.hamcrest.beans.HasPropertyWithValue.hasProperty;
import static org.hamcrest.collection.IsIterableContainingInAnyOrder.containsInAnyOrder;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertThat;

import java.io.File;
import java.util.LinkedList;
import java.util.List;
import org.junit.Before;
import org.junit.Test;

/** Class for JUnit tests of Project controller and its dependencies */
public class ProjectControllerTest {
  // prepear tests
  ProjectController testProjectController = new ProjectController();
  List<String> testProjects = new LinkedList<String>();
  File testFile = new File("projects/HelloWorld");

  @Before
  public void setup() {
    testProjects.add("HelloWorld");
    testProjects.add("My Project");
    testProjects.add("JMLProject");
    testProjects.add("SimpleJML");
  }

  /** Execute tests! */
  @Test
  public void test() {
    // Testing listProjects()
    assertThat(
        "The server contains the default project folders",
        testProjectController.listProjects(),
        containsInAnyOrder(testProjects.toArray()));

    // Testing showProject()
    assertThat(
        "Project HelloWorld contains the file LICENSE",
        testProjectController.showProject("HelloWorld", null).contents,
        hasItem(allOf(hasProperty("name", is("LICENSE")), hasProperty("type", is("file")))));

    assertThat(
        "Project HelloWorld contains the folder src",
        testProjectController.showProject("HelloWorld", null).contents,
        hasItem(allOf(hasProperty("name", is("src")), hasProperty("type", is("folder")))));

    // Testing createFolderItem
    assertEquals("folder", testProjectController.createFolderItem(testFile).gettype());
    assertEquals("HelloWorld", testProjectController.createFolderItem(testFile).getName());
    assertThat(
        "Folder Item projects/HelloWorld contains the file LICENSE",
        testProjectController.createFolderItem(testFile).getContents(),
        hasItem(hasProperty("name", is("LICENSE"))));

    // Testing selectProjectFromArray
    assertEquals(
        "src", testProjectController.selectProjectFromArray(testFile.listFiles(), "src").getName());
  }
}
