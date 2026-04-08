import "./styles.css";

import { renderDotToSvg as defaultRenderDotToSvg } from "./render";

const SAMPLE_TRE = "(a ; b)%[1, 3)";

export interface AppDependencies {
  translateTreToDot(input: string): Promise<string>;
  translateTreToJani(input: string): Promise<string>;
  renderDotToSvg(dot: string): Promise<string>;
}

interface Tre2taWasmModule {
  default(input?: unknown): Promise<unknown>;
  treToDot(input: string): string;
  treToJani(input: string): string;
}

function toMessage(error: unknown): string {
  if (error instanceof Error) {
    return error.message;
  }
  return String(error);
}

function placeholderNode(message: string): HTMLParagraphElement {
  const node = document.createElement("p");
  node.className = "render-placeholder";
  node.textContent = message;
  return node;
}

export function bootstrapApp(root: HTMLElement, dependencies: AppDependencies): void {
  let latestDot: string | null = null;
  let latestJani: string | null = null;

  root.innerHTML = `
    <main class="container shell">
      <header class="hero">
        <p class="eyebrow">TRE2TA</p>
        <h1>TRE2TA: an online translator of TREs into TAs</h1>
        <p class="lead">
          Enter a timed regular expression, inspect the generated Graphviz source,
          preview the automaton, and export as DOT or JANI.
        </p>
      </header>

      <section class="grid workspace">
        <article>
          <header class="section-header">
            <h2>Timed regular expression</h2>
          </header>
          <form class="editor" data-role="form">
            <div class="field">
              <label class="visually-hidden" for="tre-input">
                Timed regular expression
              </label>
              <textarea
                id="tre-input"
                class="tre-input"
                name="tre"
                rows="8"
                spellcheck="false"
                data-role="tre-input"
              >${SAMPLE_TRE}</textarea>
            </div>

            <div class="controls">
              <div class="grid action-grid">
                <button type="submit" data-role="submit">Generate TA</button>
                <button
                  class="secondary outline"
                  type="button"
                  data-role="download-jani"
                  disabled
                >
                  Download JANI
                </button>
              </div>
              <label class="toggle">
                <input type="checkbox" data-role="render-toggle" checked />
                <span>Show graph preview</span>
              </label>
            </div>
          </form>

          <div class="status-stack">
            <p class="status" data-role="status">Ready to translate.</p>
            <p class="error" data-role="error" hidden></p>
            <p class="error error--soft" data-role="render-error" hidden></p>
          </div>
        </article>

        <article>
          <header class="section-header">
            <h2>Syntax sketch</h2>
          </header>
          <pre class="syntax-block">atom          a
concat        a ; b
union         a | b
intersection  a & b
star          (a ; b)*
plus          (a ; b)+
interval      (a ; b)%[1, 3)
inequality    (a | b)%(>= 5)</pre>
          <p class="syntax-note">Parentheses can be used to group subexpressions.</p>
        </article>
      </section>

      <section class="grid results">
        <article>
          <header class="section-header">
            <div class="section-header__row">
              <h2>Graphviz source</h2>
              <div class="header-actions" role="group" aria-label="DOT actions">
                <button class="secondary outline" type="button" data-role="copy" disabled>
                  Copy DOT
                </button>
                <button
                  class="secondary outline"
                  type="button"
                  data-role="download-dot"
                  disabled
                >
                  Download DOT
                </button>
              </div>
            </div>
          </header>
          <pre class="output-block" data-role="dot-output">DOT output will appear here.</pre>
        </article>

        <article>
          <header class="section-header">
            <h2>Rendered graph</h2>
          </header>
          <div class="render-pane is-empty" data-role="render-pane"></div>
        </article>
      </section>
    </main>
  `;

  const form = root.querySelector<HTMLFormElement>("[data-role='form']")!;
  const input = root.querySelector<HTMLTextAreaElement>("[data-role='tre-input']")!;
  const submitButton = root.querySelector<HTMLButtonElement>("[data-role='submit']")!;
  const copyButton = root.querySelector<HTMLButtonElement>("[data-role='copy']")!;
  const downloadDotButton =
    root.querySelector<HTMLButtonElement>("[data-role='download-dot']")!;
  const downloadJaniButton =
    root.querySelector<HTMLButtonElement>("[data-role='download-jani']")!;
  const renderToggle = root.querySelector<HTMLInputElement>("[data-role='render-toggle']")!;
  const status = root.querySelector<HTMLElement>("[data-role='status']")!;
  const error = root.querySelector<HTMLElement>("[data-role='error']")!;
  const renderError = root.querySelector<HTMLElement>("[data-role='render-error']")!;
  const dotOutput = root.querySelector<HTMLElement>("[data-role='dot-output']")!;
  const renderPane = root.querySelector<HTMLElement>("[data-role='render-pane']")!;

  const setStatus = (message: string) => {
    status.textContent = message;
  };

  const setError = (message: string | null) => {
    error.hidden = message === null;
    error.textContent = message ?? "";
  };

  const setRenderError = (message: string | null) => {
    renderError.hidden = message === null;
    renderError.textContent = message ?? "";
  };

  const setArtifacts = (dot: string | null, jani: string | null) => {
    latestDot = dot;
    latestJani = jani;
    dotOutput.textContent = dot ?? "DOT output will appear here.";
    copyButton.disabled = dot === null;
    downloadDotButton.disabled = dot === null;
    downloadJaniButton.disabled = jani === null;
  };

  const showPlaceholder = (message: string) => {
    renderPane.classList.add("is-empty");
    renderPane.replaceChildren(placeholderNode(message));
  };

  const showSvg = (svgMarkup: string) => {
    renderPane.classList.remove("is-empty");
    renderPane.innerHTML = svgMarkup;
  };

  const renderGraph = async (dot: string) => {
    if (!renderToggle.checked) {
      showPlaceholder("Graph preview is disabled.");
      setStatus("Translation is ready.");
      return;
    }

    setStatus("Rendering graph preview...");
    setRenderError(null);
    showPlaceholder("Rendering graph preview...");

    try {
      const svg = await dependencies.renderDotToSvg(dot);
      showSvg(svg);
      setStatus("Translation and graph preview are ready.");
    } catch (renderFailure) {
      showPlaceholder("Preview failed, but the translated outputs are still available.");
      setRenderError(`Rendering failed: ${toMessage(renderFailure)}`);
      setStatus("Translation is ready, but the graph preview failed.");
    }
  };

  const runTranslation = async () => {
    const source = input.value.trim();

    if (!source) {
      setError("Enter a timed regular expression to translate.");
      setRenderError(null);
      setArtifacts(null, null);
      showPlaceholder("Add a TRE and generate its automaton.");
      setStatus("Waiting for input.");
      return;
    }

    submitButton.disabled = true;
    setError(null);
    setRenderError(null);
    setStatus("Translating...");

    try {
      const [dot, jani] = await Promise.all([
        dependencies.translateTreToDot(source),
        dependencies.translateTreToJani(source),
      ]);
      setArtifacts(dot, jani);
      await renderGraph(dot);
    } catch (translationFailure) {
      setArtifacts(null, null);
      showPlaceholder("Fix the TRE and try again.");
      setError(toMessage(translationFailure));
      setStatus("Translation failed.");
    } finally {
      submitButton.disabled = false;
    }
  };

  form.addEventListener("submit", (event) => {
    event.preventDefault();
    void runTranslation();
  });

  renderToggle.addEventListener("change", () => {
    setRenderError(null);

    if (latestDot === null) {
      showPlaceholder(
        renderToggle.checked
          ? "Generate a timed automaton to preview the graph."
          : "Graph preview is disabled.",
      );
      return;
    }

    if (renderToggle.checked) {
      void renderGraph(latestDot);
      return;
    }

    showPlaceholder("Graph preview is disabled.");
    setStatus("Translation is ready.");
  });

  copyButton.addEventListener("click", async () => {
    if (latestDot === null) {
      return;
    }

    if (!navigator.clipboard?.writeText) {
      setError("Clipboard access is not available in this browser.");
      return;
    }

    try {
      await navigator.clipboard.writeText(latestDot);
      setStatus("DOT copied to the clipboard.");
    } catch (copyFailure) {
      setError(`Could not copy DOT: ${toMessage(copyFailure)}`);
    }
  });

  downloadDotButton.addEventListener("click", () => {
    if (latestDot === null) {
      return;
    }

    const blob = new Blob([latestDot], { type: "text/vnd.graphviz" });
    const url = URL.createObjectURL(blob);
    const link = document.createElement("a");
    link.href = url;
    link.download = "timed-automaton.dot";
    link.click();
    URL.revokeObjectURL(url);
    setStatus("DOT download started.");
  });

  downloadJaniButton.addEventListener("click", () => {
    if (latestJani === null) {
      return;
    }

    const blob = new Blob([latestJani], { type: "application/json" });
    const url = URL.createObjectURL(blob);
    const link = document.createElement("a");
    link.href = url;
    link.download = "timed-automaton.jani";
    link.click();
    URL.revokeObjectURL(url);
    setStatus("JANI download started.");
  });

  showPlaceholder("Generate a timed automaton to preview the graph.");
}

async function loadWasmModule(): Promise<Tre2taWasmModule> {
  const wasmModuleUrl = `${import.meta.env.BASE_URL}pkg/tre2ta_wasm.js`;
  return import(/* @vite-ignore */ wasmModuleUrl) as Promise<Tre2taWasmModule>;
}

async function createDefaultDependencies(): Promise<AppDependencies> {
  const wasm = await loadWasmModule();
  await wasm.default();

  return {
    translateTreToDot: async (input: string) => wasm.treToDot(input),
    translateTreToJani: async (input: string) => wasm.treToJani(input),
    renderDotToSvg: defaultRenderDotToSvg,
  };
}

async function mountDefaultApp(root: HTMLElement): Promise<void> {
  root.innerHTML = `
    <main class="container shell boot">
      <article aria-busy="true">
        <p class="eyebrow">TRE2TA</p>
        <h1>Loading translator...</h1>
        <p class="lead boot-copy">Preparing the online translator.</p>
      </article>
    </main>
  `;

  try {
    const dependencies = await createDefaultDependencies();
    bootstrapApp(root, dependencies);
  } catch (failure) {
    root.innerHTML = `
      <main class="container shell boot">
        <article>
          <p class="eyebrow">TRE2TA</p>
          <h1>Could not load the translator.</h1>
          <p class="error" data-role="boot-error"></p>
        </article>
      </main>
    `;

    const message = root.querySelector<HTMLElement>("[data-role='boot-error']")!;
    message.textContent = `The page could not finish loading. ${toMessage(failure)}`;
  }
}

const root = document.querySelector<HTMLElement>("#app");
if (root) {
  void mountDefaultApp(root);
}
