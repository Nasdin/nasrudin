import { afterEach, describe, expect, it, vi } from 'vitest';
import { detectPlatform, type Platform } from './RunWorker.platform';

afterEach(() => {
  vi.unstubAllGlobals();
});

function stubNavigator(stub: Partial<Navigator>) {
  vi.stubGlobal('navigator', stub as Navigator);
}

describe('detectPlatform', () => {
  it('returns null when navigator is undefined (SSR)', () => {
    vi.stubGlobal('navigator', undefined);
    expect(detectPlatform()).toBeNull();
  });

  it('detects macOS as aarch64 from a Safari UA (Apple Silicon default)', () => {
    stubNavigator({
      platform: 'MacIntel',
      userAgent:
        'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 Safari/605.1.15',
    });
    // Apple Silicon Safari still reports `MacIntel` and `Intel Mac OS X`.
    // Browsers cannot reliably distinguish — default macOS to aarch64
    // (Apple-Silicon has been the default since 2020); Intel-Mac users
    // pick the x86_64 build via the "Show all builds" disclosure.
    expect(detectPlatform()).toEqual<Platform>({ os: 'macos', arch: 'aarch64' });
  });

  it('detects macOS as aarch64 from a Chrome UA (same default — browsers strip arch)', () => {
    stubNavigator({
      platform: 'MacIntel',
      userAgent:
        'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 Chrome/120 Safari/537.36',
    });
    expect(detectPlatform()).toEqual<Platform>({ os: 'macos', arch: 'aarch64' });
  });

  it('detects Windows x86_64 from Chrome UA', () => {
    stubNavigator({
      platform: 'Win32',
      userAgent:
        'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/120 Safari/537.36',
    });
    expect(detectPlatform()).toEqual<Platform>({ os: 'windows', arch: 'x86_64' });
  });

  it('detects Linux x86_64 from Firefox UA', () => {
    stubNavigator({
      platform: 'Linux x86_64',
      userAgent: 'Mozilla/5.0 (X11; Linux x86_64; rv:120.0) Gecko/20100101 Firefox/120.0',
    });
    expect(detectPlatform()).toEqual<Platform>({ os: 'linux', arch: 'x86_64' });
  });

  it('detects Linux aarch64 from a Linux ARM UA', () => {
    stubNavigator({
      platform: 'Linux aarch64',
      userAgent: 'Mozilla/5.0 (X11; Linux aarch64; rv:120.0) Gecko/20100101 Firefox/120.0',
    });
    expect(detectPlatform()).toEqual<Platform>({ os: 'linux', arch: 'aarch64' });
  });

  it('returns null for Android (not a supported worker target)', () => {
    stubNavigator({
      platform: 'Linux armv8l',
      userAgent:
        'Mozilla/5.0 (Linux; Android 14; Pixel 8) AppleWebKit/537.36 Chrome/120 Mobile Safari/537.36',
    });
    expect(detectPlatform()).toBeNull();
  });
});
