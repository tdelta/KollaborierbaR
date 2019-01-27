package events;

import org.springframework.context.ApplicationEvent;

public class UpdatedFileEvent extends ProjectEvent {
    private final String filePath;

    public UpdatedFileEvent(final Object source, final String projectName, final String filePath) {
        super(source, "UpdatedFileEvent", projectName);
        this.filePath = filePath;
    }

    public String getFilePath() {
        return filePath;
    }
}
