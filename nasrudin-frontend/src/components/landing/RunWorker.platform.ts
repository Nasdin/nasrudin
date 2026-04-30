export type OsKind = 'macos' | 'linux' | 'windows';
export type ArchKind = 'x86_64' | 'aarch64';

export interface Platform {
  os: OsKind;
  arch: ArchKind;
}

/**
 * Best-effort platform detection from `navigator`. Returns `null` when
 * navigator is missing (SSR) or the platform is not a supported worker target.
 *
 * Notes:
 * - macOS: defaults to aarch64 (Apple Silicon has been the default since 2020).
 *   Browsers cannot reliably distinguish Intel from Apple Silicon — the Show
 *   All Builds disclosure on the page lets Intel users pick the x86_64 SKU.
 * - Linux: arch is derived from the literal UA / platform string.
 * - Windows: only x86_64 is shipped; UA arch is not used to gate detection.
 */
export function detectPlatform(): Platform | null {
  if (typeof navigator === 'undefined' || !navigator) return null;

  const ua = navigator.userAgent ?? '';
  const platform = navigator.platform ?? '';

  // Android masquerades as Linux on userAgent.platform — exclude it.
  if (/Android/i.test(ua)) return null;

  const isMac = /Mac/i.test(platform) || /Macintosh/i.test(ua);
  const isWin = /Win/i.test(platform) || /Windows/i.test(ua);
  const isLinux = /Linux/i.test(platform) && !isMac;

  if (isMac) return { os: 'macos', arch: 'aarch64' };
  if (isWin) return { os: 'windows', arch: 'x86_64' };
  if (isLinux) {
    const arm = /aarch64|arm64|armv8/i.test(`${platform} ${ua}`);
    return { os: 'linux', arch: arm ? 'aarch64' : 'x86_64' };
  }
  return null;
}
