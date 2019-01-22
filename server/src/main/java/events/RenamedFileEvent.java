package events;

import org.springframework.context.ApplicationEvent;

public class RenamedFileEvent extends ProjectEvent {
    private final String originalPath;
    private final String newPath;

    public RenamedFileEvent(
        final Object source,
        final String projectName,
        final String originalPath,
        final String newPath
    ) {
        super(
            source,
            "RenamedFileEvent",
            projectName
        );

        this.originalPath = originalPath;
        this.newPath = newPath;
    }

    public String getOriginalPath() {
        return originalPath;
    }

    public String getNewPath() {
        return newPath;
    }
}
