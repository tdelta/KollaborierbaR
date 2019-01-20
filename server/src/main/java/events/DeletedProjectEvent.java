package events;

import org.springframework.context.ApplicationEvent;

public class DeletedProjectEvent extends ApplicationEvent {
    private String projectPath;

    public DeletedProjectEvent(final Object source, final String projectPath) {
        super(source);
        this.projectPath = projectPath;
    }

    public String getProjectPath() {
        return projectPath;
    }
}
