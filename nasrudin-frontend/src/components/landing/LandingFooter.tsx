export function LandingFooter() {
  return (
    <footer className="footer">
      <div className="container-wide">
        <div className="footer-grid">
          <div>
            <div className="footer-brand">Nasrud·in</div>
            <div className="footer-tag">
              Named for the wise fool who found truth by walking the long way round.
            </div>
          </div>
          <div className="footer-col">
            <h5>Project</h5>
            <ul>
              <li>
                <a href="#how">How it works</a>
              </li>
              <li>
                <a href="#discoveries">Rediscoveries</a>
              </li>
              <li>
                <a href="#network">The network</a>
              </li>
              <li>
                <a href="#run">Run a worker</a>
              </li>
            </ul>
          </div>
          <div className="footer-col">
            <h5>For researchers</h5>
            <ul>
              <li>
                <a href="/browse">Browse corpus</a>
              </li>
              <li>
                <a href="/api-docs">API & data</a>
              </li>
              <li>
                <a href="/api-keys">API keys</a>
              </li>
              <li>
                <a href="/pricing">Pricing</a>
              </li>
            </ul>
          </div>
          <div className="footer-col">
            <h5>Open</h5>
            <ul>
              <li>
                <a href="https://github.com/nasdin/nasrudin">Source · github</a>
              </li>
              <li>
                <a href="/leaderboard">Contributors</a>
              </li>
              <li>
                <a href="#run">Roadmap</a>
              </li>
              <li>
                <a href="/signin">Sign in</a>
              </li>
            </ul>
          </div>
          <div className="footer-col">
            <h5>Contact</h5>
            <ul>
              <li>
                <a href="mailto:nasrudinsalim@nasrudin.org">Email us</a>
              </li>
            </ul>
          </div>
        </div>
        <div className="footer-bottom">
          <span>Built in Rust + Lean 4 · open source · MIT licensed.</span>
          <span>v0.4.2 · 2026 · "Because the light is better here."</span>
        </div>
      </div>
    </footer>
  );
}
