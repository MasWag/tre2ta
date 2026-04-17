import { defineConfig } from "vitest/config";

export default defineConfig(({ command }) => ({
  base: command === "build" ? "/tre2ta/" : "/",
  test: {
    environment: "jsdom",
    globals: true,
    css: true,
  },
}));
