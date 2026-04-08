import { createDotRenderer } from "./render";

describe("createDotRenderer", () => {
  it("reuses the same renderer instance", async () => {
    let loads = 0;
    const renderDotToSvg = createDotRenderer(async () => {
      loads += 1;
      return {
        renderString: (dot: string) => `<svg data-dot="${dot}"></svg>`,
      };
    });

    await expect(renderDotToSvg("digraph { q0 -> q1 }")).resolves.toContain("<svg");
    await expect(renderDotToSvg("digraph { q1 -> q2 }")).resolves.toContain("<svg");
    expect(loads).toBe(1);
  });
});
