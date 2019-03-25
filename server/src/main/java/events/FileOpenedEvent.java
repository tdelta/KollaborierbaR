package events;

import java.security.Principal;
import org.springframework.context.ApplicationEvent;

public class FileOpenedEvent extends ApplicationEvent {

  private Principal principal;
  private String file;

  public FileOpenedEvent(final Object source, final Principal principal, final String file) {
    super(source);
    this.principal = principal;
    this.file = file;
  }

  public Principal getPrincipal() {
    return principal;
  }

  public String getFile() {
    return file;
  }
}
