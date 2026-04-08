interface VizRenderer {
  renderString(
    dot: string,
    options?: {
      engine?: string;
      format?: string;
    },
  ): Promise<string> | string;
}

type VizLoader = () => Promise<VizRenderer>;

async function loadVizRenderer(): Promise<VizRenderer> {
  const { instance } = await import("@viz-js/viz");
  return instance();
}

export function createDotRenderer(loader: VizLoader = loadVizRenderer) {
  let rendererPromise: Promise<VizRenderer> | undefined;

  return async (dot: string): Promise<string> => {
    rendererPromise ??= loader();
    const renderer = await rendererPromise;
    return renderer.renderString(dot, {
      engine: "dot",
      format: "svg",
    });
  };
}

export const renderDotToSvg = createDotRenderer();
