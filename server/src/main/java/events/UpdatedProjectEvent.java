package events;

import org.springframework.context.ApplicationEvent;

public class UpdatedProjectEvent extends ProjectEvent {
    public UpdatedProjectEvent(final Object source, final String projectName) {
        super(source, "UpdatedProjectEvent", projectName);
    }
}
