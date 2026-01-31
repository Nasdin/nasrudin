import { Store } from "@tanstack/store";

// ── UI Store ──────────────────────────────────────────────
export interface UIState {
	sidebarOpen: boolean;
	selectedDomain: string | null;
	derivationTab: "tree" | "steps" | "lean";
}

export const uiStore = new Store<UIState>({
	sidebarOpen: false,
	selectedDomain: null,
	derivationTab: "tree",
});

// ── GA Engine Live State ──────────────────────────────────
// SSE discovery events and engine run status that multiple components read
export interface EngineUIState {
	isStreaming: boolean;
	lastEventTimestamp: number | null;
	eventCount: number;
}

export const engineUIStore = new Store<EngineUIState>({
	isStreaming: false,
	lastEventTimestamp: null,
	eventCount: 0,
});
