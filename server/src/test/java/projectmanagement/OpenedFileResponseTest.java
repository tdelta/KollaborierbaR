package projectmanagement;

import org.junit.Test;

import static org.junit.Assert.assertThat;
import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.CoreMatchers.equalTo;

import projectmanagement.OpenedFileResponse;

/**
 * Testing the OpenedFile data container class.
 * It shall just store information and not modify it.
 */
public class OpenedFileResponseTest {
  @Test
  public void testGetters() {
    final String filename = "README.md";
    final String contents = "Hello World";

    final OpenedFileResponse ofile = new OpenedFileResponse(filename, contents);

    assertThat(
      ofile.getFileName(),
      is(equalTo(filename))
    );

    assertThat(
      ofile.getFileText(),
      is(equalTo(contents))
    );
  }
}
