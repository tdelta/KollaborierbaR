public class DosTest {
  private void provokeWarning() {
    switch (1) {
      case 1:
        System.out.println("Hello World");
      case 2: // There's a fall-through warning around here
        break;
    }
  }
}
