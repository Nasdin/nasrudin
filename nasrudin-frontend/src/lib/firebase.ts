/**
 * Firebase Web SDK wrapper. Lazy-init so SSR (TanStack Start) doesn't try
 * to construct the Firebase app on the server. All exports are
 * browser-only — call them from inside event handlers or mutations, not
 * from route loaders.
 *
 * Env vars (all required, all public per Firebase's threat model):
 *   VITE_FIREBASE_API_KEY
 *   VITE_FIREBASE_AUTH_DOMAIN
 *   VITE_FIREBASE_PROJECT_ID
 *   VITE_FIREBASE_STORAGE_BUCKET
 *   VITE_FIREBASE_MESSAGING_SENDER_ID
 *   VITE_FIREBASE_APP_ID
 */

import { type FirebaseApp, getApps, initializeApp } from 'firebase/app';
import {
  GoogleAuthProvider,
  type Auth,
  type UserCredential,
  createUserWithEmailAndPassword,
  getAuth,
  sendEmailVerification,
  sendPasswordResetEmail,
  signInWithEmailAndPassword,
  signInWithPopup,
  signOut as fbSignOut,
} from 'firebase/auth';

let appSingleton: FirebaseApp | undefined;

function envVar(name: string): string {
  const v = (import.meta.env as Record<string, string | undefined>)[name];
  if (!v) throw new Error(`Missing env var: ${name}`);
  return v;
}

function getFirebaseApp(): FirebaseApp {
  if (typeof window === 'undefined') {
    throw new Error('Firebase Web SDK is browser-only');
  }
  if (appSingleton) return appSingleton;
  const existing = getApps();
  const first = existing[0];
  if (first) {
    appSingleton = first;
    return appSingleton;
  }
  appSingleton = initializeApp({
    apiKey: envVar('VITE_FIREBASE_API_KEY'),
    authDomain: envVar('VITE_FIREBASE_AUTH_DOMAIN'),
    projectId: envVar('VITE_FIREBASE_PROJECT_ID'),
    storageBucket: envVar('VITE_FIREBASE_STORAGE_BUCKET'),
    messagingSenderId: envVar('VITE_FIREBASE_MESSAGING_SENDER_ID'),
    appId: envVar('VITE_FIREBASE_APP_ID'),
  });
  return appSingleton;
}

function getFirebaseAuth(): Auth {
  return getAuth(getFirebaseApp());
}

export async function signInWithEmail(
  email: string,
  password: string,
): Promise<UserCredential> {
  return signInWithEmailAndPassword(getFirebaseAuth(), email, password);
}

export async function signUpWithEmail(
  email: string,
  password: string,
): Promise<UserCredential> {
  return createUserWithEmailAndPassword(getFirebaseAuth(), email, password);
}

export async function signInWithGoogle(): Promise<UserCredential> {
  const provider = new GoogleAuthProvider();
  return signInWithPopup(getFirebaseAuth(), provider);
}

export async function sendPasswordReset(email: string): Promise<void> {
  return sendPasswordResetEmail(getFirebaseAuth(), email);
}

export async function sendVerificationEmail(): Promise<void> {
  const user = getFirebaseAuth().currentUser;
  if (!user) throw new Error('Not signed in');
  return sendEmailVerification(user);
}

export async function firebaseSignOut(): Promise<void> {
  return fbSignOut(getFirebaseAuth());
}

/**
 * Returns a fresh ID token (refreshed if near expiry). Throws if no user
 * is signed in.
 */
export async function getCurrentIdToken(): Promise<string> {
  const user = getFirebaseAuth().currentUser;
  if (!user) throw new Error('Not signed in');
  return user.getIdToken(/* forceRefresh */ false);
}

/**
 * Map Firebase error codes to user-facing messages. Used by hooks /
 * forms to render inline errors.
 */
export function firebaseErrorMessage(err: unknown): string {
  const code = (err as { code?: string } | null)?.code;
  switch (code) {
    case 'auth/invalid-credential':
    case 'auth/wrong-password':
    case 'auth/user-not-found':
      return 'Email or password is incorrect.';
    case 'auth/email-already-in-use':
      return 'That email already has an account. Try signing in instead.';
    case 'auth/weak-password':
      return 'Password is too weak. Use at least 8 characters.';
    case 'auth/invalid-email':
      return 'That email address looks invalid.';
    case 'auth/too-many-requests':
      return 'Too many attempts. Try again in a few minutes.';
    case 'auth/popup-closed-by-user':
    case 'auth/cancelled-popup-request':
      return 'Sign-in cancelled.';
    case 'auth/network-request-failed':
      return 'Network error. Check your connection and try again.';
    default:
      return (err as Error)?.message ?? 'Sign-in failed.';
  }
}
