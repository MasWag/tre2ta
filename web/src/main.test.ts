import { bootstrapApp, type AppDependencies } from "./main";

const flush = async () => {
  await Promise.resolve();
  await new Promise((resolve) => setTimeout(resolve, 0));
};

function renderApp(overrides: Partial<AppDependencies> = {}) {
  const root = document.createElement("div");
  const dependencies: AppDependencies = {
    translateTreToDot: async () => "digraph timed_automaton { q0 -> q1; }",
    translateTreToJani: async () => '{"jani-version":1}',
    renderDotToSvg: async () => "<svg viewBox=\"0 0 10 10\"></svg>",
    ...overrides,
  };

  bootstrapApp(root, dependencies);
  return { root, dependencies };
}

describe("bootstrapApp", () => {
  afterEach(() => {
    vi.restoreAllMocks();
  });

  it("writes DOT output from the textarea input", async () => {
    const translateTreToDot = vi.fn(
      async (input: string) => `digraph timed_automaton { label="${input}"; }`,
    );
    const translateTreToJani = vi.fn(async () => '{"jani-version":1}');
    const { root } = renderApp({ translateTreToDot, translateTreToJani });

    const form = root.querySelector<HTMLFormElement>("[data-role='form']")!;
    const input = root.querySelector<HTMLTextAreaElement>("[data-role='tre-input']")!;
    const output = root.querySelector<HTMLElement>("[data-role='dot-output']")!;

    input.value = "a ; b";
    form.dispatchEvent(new Event("submit", { bubbles: true, cancelable: true }));
    await flush();

    expect(translateTreToDot).toHaveBeenCalledWith("a ; b");
    expect(translateTreToJani).toHaveBeenCalledWith("a ; b");
    expect(output.textContent).toContain('label="a ; b"');
  });

  it("renders the graph only when rendering is enabled", async () => {
    const renderDotToSvg = vi.fn(async () => "<svg viewBox=\"0 0 10 10\"></svg>");
    const { root } = renderApp({ renderDotToSvg });

    const form = root.querySelector<HTMLFormElement>("[data-role='form']")!;
    const toggle = root.querySelector<HTMLInputElement>("[data-role='render-toggle']")!;
    const pane = root.querySelector<HTMLElement>("[data-role='render-pane']")!;

    toggle.checked = false;
    toggle.dispatchEvent(new Event("change", { bubbles: true }));
    form.dispatchEvent(new Event("submit", { bubbles: true, cancelable: true }));
    await flush();

    expect(renderDotToSvg).not.toHaveBeenCalled();
    expect(pane.textContent).toContain("Graph preview is disabled.");

    toggle.checked = true;
    toggle.dispatchEvent(new Event("change", { bubbles: true }));
    await flush();

    expect(renderDotToSvg).toHaveBeenCalledTimes(1);
    expect(pane.innerHTML).toContain("<svg");
  });

  it("keeps raw DOT visible when rendering fails", async () => {
    const { root } = renderApp({
      translateTreToDot: async () => "digraph timed_automaton { q0 -> q1; }",
      translateTreToJani: async () => '{"jani-version":1}',
      renderDotToSvg: async () => {
        throw new Error("renderer exploded");
      },
    });

    const form = root.querySelector<HTMLFormElement>("[data-role='form']")!;
    const output = root.querySelector<HTMLElement>("[data-role='dot-output']")!;
    const renderError = root.querySelector<HTMLElement>("[data-role='render-error']")!;

    form.dispatchEvent(new Event("submit", { bubbles: true, cancelable: true }));
    await flush();

    expect(output.textContent).toContain("digraph timed_automaton");
    expect(renderError.textContent).toContain("Rendering failed:");
  });

  it("places DOT actions in the Graphviz source section", () => {
    const { root } = renderApp();
    const graphvizSection = root.querySelector<HTMLElement>("[data-role='dot-output']")!.closest(
      "article",
    )!;

    expect(graphvizSection.querySelector("[data-role='copy']")).not.toBeNull();
    expect(graphvizSection.querySelector("[data-role='download-dot']")).not.toBeNull();
  });

  it("downloads JANI after a successful translation", async () => {
    const createObjectURL = vi.fn(() => "blob:jani-download");
    const revokeObjectURL = vi.fn();
    const click = vi.spyOn(HTMLAnchorElement.prototype, "click").mockImplementation(() => {});
    const originalCreateObjectURL = URL.createObjectURL;
    const originalRevokeObjectURL = URL.revokeObjectURL;

    Object.defineProperty(URL, "createObjectURL", {
      value: createObjectURL,
      configurable: true,
    });
    Object.defineProperty(URL, "revokeObjectURL", {
      value: revokeObjectURL,
      configurable: true,
    });

    try {
      const { root } = renderApp();
      const form = root.querySelector<HTMLFormElement>("[data-role='form']")!;
      const downloadButton =
        root.querySelector<HTMLButtonElement>("[data-role='download-jani']")!;
      const status = root.querySelector<HTMLElement>("[data-role='status']")!;

      form.dispatchEvent(new Event("submit", { bubbles: true, cancelable: true }));
      await flush();

      downloadButton.click();

      expect(createObjectURL).toHaveBeenCalledOnce();
      expect(click).toHaveBeenCalledOnce();
      expect(revokeObjectURL).toHaveBeenCalledWith("blob:jani-download");
      expect(status.textContent).toContain("JANI download started.");
    } finally {
      Object.defineProperty(URL, "createObjectURL", {
        value: originalCreateObjectURL,
        configurable: true,
      });
      Object.defineProperty(URL, "revokeObjectURL", {
        value: originalRevokeObjectURL,
        configurable: true,
      });
    }
  });
});
