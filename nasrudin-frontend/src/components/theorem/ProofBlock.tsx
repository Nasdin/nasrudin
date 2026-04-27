export function ProofBlock({ source }: { source: string }) {
  return (
    <pre className="thm-proof-pre" style={{ whiteSpace: 'pre-wrap' }}>
      {source}
    </pre>
  );
}
