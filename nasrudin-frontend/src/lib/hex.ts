/**
 * Helpers for converting between the byte-array form that the server uses to
 * serialize `BYTEA` (default `Vec<u8>` → JSON array of byte numbers) and the
 * lower-case hex string form that the rest of the frontend expects for URLs,
 * React keys, and human-readable display.
 *
 * The Phase 9 `theorems` API returns `id`, `canonical_hash`, and each parent
 * id as `number[]`; whenever the UI needs to route to `/theorem/$id` or render
 * `thm:abcd1234`, it should pass the value through `bytesToHex` first.
 */

/** Lower-case hex-encode a byte array (length-agnostic). */
export function bytesToHex(bytes: number[]): string {
  let out = '';
  for (const b of bytes) {
    out += (b & 0xff).toString(16).padStart(2, '0');
  }
  return out;
}

/**
 * Decode a lower-case hex string back to a byte array.
 *
 * Throws if `s` has odd length or contains non-hex characters. Mostly useful
 * for tests; production code only ever needs the encode direction.
 */
export function hexToBytes(s: string): number[] {
  if (s.length % 2 !== 0) throw new Error(`hex: odd length ${s.length}`);
  const out: number[] = [];
  for (let i = 0; i < s.length; i += 2) {
    const byte = Number.parseInt(s.slice(i, i + 2), 16);
    if (Number.isNaN(byte)) throw new Error(`hex: bad byte at offset ${i}`);
    out.push(byte);
  }
  return out;
}
