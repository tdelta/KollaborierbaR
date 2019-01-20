package events;

import org.springframework.context.ApplicationEvent;

public class UpdatedProjectEvent extends ApplicationEvent {
    private String projectPath;

    public UpdatedProjectEvent(final Object source, final String projectPath) {
        super(source);
        this.projectPath = projectPath;
    }

    public String getProjectPath() {
        return projectPath;
    }
}
