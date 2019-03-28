package server;

import events.DeletedFileEvent;
import events.DeletedProjectEvent;
import events.RenamedFileEvent;
import events.UpdatedFileEvent;
import events.UpdatedProjectEvent;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.util.LinkedList;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Scanner;
import javax.servlet.http.HttpServletRequest;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.context.ApplicationEventPublisher;
import org.springframework.http.HttpStatus;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.CrossOrigin;
import org.springframework.web.bind.annotation.PathVariable;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestMethod;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.ResponseBody;
import org.springframework.web.bind.annotation.RestController;
import org.springframework.web.servlet.HandlerMapping;
import projectmanagement.FileItem;
import projectmanagement.FileUpdateData;
import projectmanagement.FolderItem;
import projectmanagement.Item;
import projectmanagement.OpenedFileResponse;

/**
 * This is a rest controller for manipulating the project file structure. This includes for example
 * deleting or adding files.
 *
 * @author Marc Arnold, David Heck
 */
@RestController
@CrossOrigin
@RequestMapping("/projects")
public class ProjectController {
  private static final String projectPath = "projects";

  @Autowired private ApplicationEventPublisher applicationEventPublisher;

  /**
   * That method handels requests to /listProjects and creates a list of project names.
   *
   * @return a List containing Stings of the Names form of the Folders in the Projects
   *     folder(currently hardcoded)
   */
  @RequestMapping(value = "", method = RequestMethod.GET)
  public List<String> listProjects() {
    final List<String> projects = new LinkedList<String>();

    final File file = new File(projectPath);
    final File[] files = file.listFiles();

    for (final File f : files) {
      projects.add(f.getName());
    }

    return projects;
  }

  /**
   * That method handles requests to /{projectname} and creates a folderItem object which models the
   * folder structure of the given folder/project name. The object will later be marshalled through
   * Java Spring, resulting in a JSON object.
   *
   * @param request is given in the http request.
   * @return the content of a chooses Projekt (currently hardcoded) in the form of a folder
   */
  @RequestMapping(value = "/{projectname}", method = RequestMethod.GET)
  public FolderItem showProject(
      @PathVariable("projectname") String projectname, HttpServletRequest request) {
    // Get the File/Folder form the file system
    final File file = new File(projectPath);
    final File[] files = file.listFiles();

    final File selected = selectProjectFromArray(files, projectname);

    return createFolderItem(selected);
  }

  /**
   * Helper function for recursivly creating a folderItem object from a given file structure.
   *
   * @param file A file from the file system
   * @return A Folder and its content
   */
  public FolderItem createFolderItem(File file) {
    final List<Item> entries = new LinkedList<Item>();

    // Adding the content of the Folder to a list if it is a file just add it if its a folder add it
    // and call the method again recursivly
    for (final File f : file.listFiles()) {
      if (f.isFile()) {
        entries.add(new FileItem(f.getName()));
      } else if (f.isDirectory()) {
        entries.add(createFolderItem(f));
      }
    }
    return new FolderItem(entries, file.getName());
  }

  /**
   * Selectes a folder/project from a given file structure and returns it.
   *
   * @param files List of the content of a folder
   * @param name Name of the to be selected Folder
   * @return The folder matching the giving name or null if it does not exist
   */
  public File selectProjectFromArray(File[] files, String name) {
    for (final File f : files) {
      if (f.getName().equals(name)) {
        return f;
      }
    }
    return null;
  }

  /**
   * That method handels request to /** (which should represend a path to a file) and returns the
   * contents of a file and its name.
   *
   * @param request to the file, which is supposed to be opened.
   * @return object containing filename and filetext (object for marshalling)
   */
  @RequestMapping(value = "/**", method = RequestMethod.GET)
  @ResponseBody
  public ResponseEntity<?> openFile(HttpServletRequest request) throws IOException {

    // Get the file path for the request resource
    String path =
        ((String) request.getAttribute(HandlerMapping.PATH_WITHIN_HANDLER_MAPPING_ATTRIBUTE))
            .substring(1);

    try {

      final File file = new File(path);

      Scanner scan = new Scanner(/*scanners allow to read a file until a delimiter*/ file, "utf-8");

      // Check whether the requested file is empty
      if (!scan.hasNext()) {
        scan.close();
        return new ResponseEntity<OpenedFileResponse>(
            new OpenedFileResponse(file.getName(), ""), HttpStatus.OK);
      }

      final String content =
          scan.useDelimiter("\\Z").next(); // read until end of file (Z delimiter)
      // ^ using a scanner may not be optimal (could cause overhead),
      //  but simplifies this code so much, that we keep it for now

      scan.close();
      return new ResponseEntity<OpenedFileResponse>(
          new OpenedFileResponse(file.getName(), content), HttpStatus.OK);
    } catch (FileNotFoundException e) {
      e.printStackTrace();
      return new ResponseEntity<String>(
          "File could not be found. The following path was used for search:" + path,
          HttpStatus.NOT_FOUND);
    } catch (NoSuchElementException e) {
      e.printStackTrace();
      return new ResponseEntity<String>(
          "Read Error. Error while reading the request file: " + path,
          HttpStatus.INTERNAL_SERVER_ERROR);
    } catch (IllegalStateException e) {
      e.printStackTrace();
      return new ResponseEntity<String>(
          "Read Error. Error while reading the request file: " + path,
          HttpStatus.INTERNAL_SERVER_ERROR);
    }
  }

  /**
   * This Method handles the creation of Files and Folders
   *
   * @param type Type of the kind of structure to be created can be file or folder
   * @param request HttpServletRequest in order to get the full path
   * @return Returns a HttpStatus depending on whether the right type was given.
   * @throws IOException when a new file could not be created
   */
  @RequestMapping(value = "/{projectname}/**", method = RequestMethod.PUT)
  @ResponseBody
  public ResponseEntity<?> createFile(
      @PathVariable("projectname") String projectname,
      @RequestParam("type") String type,
      HttpServletRequest request)
      throws IOException {

    // Removes the first character from the path string, we need this because java.io.File need a
    // path that does not start with a "/"
    String path =
        ((String) request.getAttribute(HandlerMapping.PATH_WITHIN_HANDLER_MAPPING_ATTRIBUTE))
            .substring(1);

    final File file = new File(path);

    // Java createNewFile and mkdir are not able to create a file if a file
    // with the same name already exists. Therefore, if someone tries to create
    // a file with the same name, return a Http Bad Request Response
    if (file.exists()) {
      return new ResponseEntity<String>(
          "There already exists a file with the same name you try to create",
          HttpStatus.BAD_REQUEST);
    }

    // check which kind of structure should be created
    if (type.equals("file")) {
      file.createNewFile();
    } else if (type.equals("folder")) {
      file.mkdir();
    } else {
      // Wrong type parameter was selected, respond with Bad request code

      return new ResponseEntity<>(
          "Wrong type parameter was choosen in the request. To create a file, please select file or folder as type.",
          HttpStatus.BAD_REQUEST);
    }

    final UpdatedProjectEvent event = new UpdatedProjectEvent(this, projectname);
    applicationEventPublisher.publishEvent(event);

    // If everything was good, return the new project structure together with a HTTP OK response
    // code
    return new ResponseEntity<FolderItem>(showProject(projectname, request), HttpStatus.OK);
  }

  /**
   * This Method handles the deletion of files and folders
   *
   * @param request HttpServletRequest in order to get the full path
   * @return Returns a HttpStatus depending on whether the file to be deleted exists.
   */
  @RequestMapping(value = "/{projectname}/**", method = RequestMethod.DELETE)
  @ResponseBody
  public ResponseEntity<?> deleteFile(
      @PathVariable("projectname") String projectname, HttpServletRequest request) {

    // Removes the first character from the path string, we need this because java.io.File need a
    // path that does not start with a "/"
    final String path =
        ((String) request.getAttribute(HandlerMapping.PATH_WITHIN_HANDLER_MAPPING_ATTRIBUTE))
            .substring(1);
    final String filePath;
    {
      final int separatorIdx = path.indexOf('/');
      if (separatorIdx == -1 || separatorIdx + 1 >= path.length()) {
        return new ResponseEntity<>(
            "A file path withing the project needs to be specified.", HttpStatus.NOT_FOUND);
      }

      filePath = path.substring(separatorIdx + 1);
    }

    final File file = new File(path);
    // check if the given path actually leads to a valid directory
    if (!file.exists()) {
      return new ResponseEntity<>(
          "The file you try to delete does not exist.", HttpStatus.NOT_FOUND);
    } else {
      try {

        List<String> deletedFiles = delete(path, file);
        final DeletedFileEvent event =
            new DeletedFileEvent(this, projectname, filePath, deletedFiles);
        applicationEventPublisher.publishEvent(event);

        return new ResponseEntity<FolderItem>(showProject(projectname, request), HttpStatus.OK);
      } catch (IOException e) {
        e.printStackTrace();
        return new ResponseEntity<>(
            "File exists, but could still not be deleted", HttpStatus.INTERNAL_SERVER_ERROR);
      }
    }
  }

  /**
   * This Method handles the deletion of projects
   *
   * @param request HttpServletRequest in order to get the full path
   * @return Returns a HttpStatus depending on whether the file to be deleted exists.
   */
  @RequestMapping(value = "/{projectname}", method = RequestMethod.DELETE)
  @ResponseBody
  public ResponseEntity<?> deleteProject(
      @PathVariable("projectname") String projectname, HttpServletRequest request) {

    // Removes the first character from the path string, we need this because java.io.File need a
    // path that does not start with a "/"
    String path =
        ((String) request.getAttribute(HandlerMapping.PATH_WITHIN_HANDLER_MAPPING_ATTRIBUTE))
            .substring(1);

    final File file = new File(path);
    // check if the given path actually leads to a valid directory
    if (!file.exists()) {
      return new ResponseEntity<>(
          "The file you try to delete does not exist.", HttpStatus.NOT_FOUND);
    } else {
      try {

        List<String> deletedFiles = delete(path, file);
        final DeletedProjectEvent event = new DeletedProjectEvent(this, projectname, deletedFiles);
        applicationEventPublisher.publishEvent(event);

        // WICHTIG: Der Grund für die Existenz dieser Funktion separat von deleteFile ist, dass wenn
        // wir ein Project löschen, wir kein neues Json Object davon zurücken können
        return new ResponseEntity<>(HttpStatus.OK);
      } catch (IOException e) {
        e.printStackTrace();
        return new ResponseEntity<>(
            "File exists, but could still not be deleted", HttpStatus.INTERNAL_SERVER_ERROR);
      }
    }
  }

  /**
   * Recursive helper method for deleting a file or folder that is called with a base path and
   * returns the absolute path of all deleted files or folders
   *
   * @param path path of the second parameter file
   * @param file file or directory to delete
   * @throws IOException exception if file cannot be deleted (for example it might not exist)
   */
  private List<String> delete(String path, File file) throws IOException {
    List<String> result = new LinkedList<>();
    // if the currenct file is not a file but a directory we need to delete its content first.
    if (file.isDirectory()) {
      // if the current directory is not empty  list its content and call delete recursively
      if (file.list().length != 0) {
        for (File f : file.listFiles()) {
          result.addAll(delete(path + "/" + f.getName(), f));
        }
      }
    }
    result.add(path);
    // if the current directory is an empty directory or a file, delete it
    final boolean deleted = file.delete();
    if (!deleted) {
      throw new IOException("Could not delete file");
    }
    return result;
  }

  /**
   * This method handles updates to files and folders. For files/folders it is possible to rename
   * the filename.
   *
   * <p>For files it is also possible to update the filecontent. But it is not possible to update
   * fileName and fileContent with one methodcall.
   *
   * <p>Example JSON for updating fileContent: { fileContent: 'Some Content' }
   *
   * <p>Example JSON for updating fileName: { fileName: 'path' }
   *
   * <p>The incoming JSON is marshalled into a FileUpdateData object.
   */
  @RequestMapping(value = "/{projectname}/**", method = RequestMethod.POST)
  @ResponseBody
  public ResponseEntity<?> updateFile(
      @PathVariable("projectname") String projectname,
      @RequestBody FileUpdateData updateData,
      HttpServletRequest request) {

    // Get the file path for the request resource
    // substring(1) remove the "/..." at the beginning of a path
    final String path =
        ((String) request.getAttribute(HandlerMapping.PATH_WITHIN_HANDLER_MAPPING_ATTRIBUTE))
            .substring(1);

    final String originalPath;
    {
      final int separatorIdx = path.indexOf('/', path.indexOf('/') + 1);
      if (separatorIdx == -1 || separatorIdx + 1 >= path.length()) {
        return new ResponseEntity<>(
            "A file path within the project needs to be specified.", HttpStatus.NOT_FOUND);
      }

      originalPath = path.substring(separatorIdx + 1);
    }

    // Rename a file or a folder
    if (updateData.fileContent == null) {

      final File file = new File(path);
      // substring(1) remove the "/..." at the beginning of a path
      final String path2 = updateData.fileName.substring(1);
      final boolean success = file.renameTo(new File(path2));

      if (success) {
        final String newPath;
        {
          final int separatorIdx = path2.indexOf('/', path2.indexOf('/') + 1);
          if (separatorIdx == -1 || separatorIdx + 1 >= path2.length()) {
            return new ResponseEntity<>(
                "A file path within the project needs to be specified as target path.",
                HttpStatus.NOT_FOUND);
          }

          newPath = path2.substring(separatorIdx + 1);
        }

        final RenamedFileEvent event =
            new RenamedFileEvent(this, projectname, originalPath, newPath);
        applicationEventPublisher.publishEvent(event);

        return new ResponseEntity<>(showProject(projectname, request), HttpStatus.OK);
      } else {
        return new ResponseEntity<>("The file could no be renamed.", HttpStatus.BAD_REQUEST);
      }
    } else {
      // If you are in this branch, the fileContent wasn't null. That implies that you do have a
      // file
      // and that the
      // caller of that functions wants to update the content, not the name of the file.
      try {
        // Oldversion: Had problems with encoding
        // final BufferedWriter writer = new BufferedWriter(new FileWriter(path));
        final File f = new File(path);
        final Writer writer =
            new OutputStreamWriter(new FileOutputStream(f), StandardCharsets.UTF_8);
        writer.write(updateData.fileContent);
        writer.close();

        final UpdatedFileEvent event = new UpdatedFileEvent(this, projectname, originalPath);
        applicationEventPublisher.publishEvent(event);

        return new ResponseEntity<>(showProject(projectname, request), HttpStatus.OK);
      } catch (IOException e) {
        e.printStackTrace();
        return new ResponseEntity<>(
            "Something went wrong while updating the file content.", HttpStatus.BAD_REQUEST);
      }
    }
  }
}
