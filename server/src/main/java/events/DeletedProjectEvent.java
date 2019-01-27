package events;

import org.springframework.context.ApplicationEvent;

public class DeletedProjectEvent extends ProjectEvent {
    public DeletedProjectEvent(final Object source, final String projectName) {
        super(source, "DeletedProjectEvent", projectName);
    }
}
