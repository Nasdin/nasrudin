import { domainPresentation } from '~/lib/domains';

interface DomainBadgeProps {
  domain: string | null | undefined;
  /** Show the category tagline below the pill. Defaults to false. */
  withTagline?: boolean;
  size?: 'sm' | 'md' | 'lg';
}

// Renders a category-coloured pill for a theorem's domain. The colour
// classes are defined in styles.css (.domain-pill, .domain-pill-<cat>) so
// the palette stays in one place. For the theorem-page hero we use size
// "lg" with the tagline visible; for ticker/table contexts use "sm".
export function DomainBadge({ domain, withTagline = false, size = 'md' }: DomainBadgeProps) {
  const { label, category, tagline } = domainPresentation(domain);
  const className = `domain-pill domain-pill-${category} domain-pill-${size}`;
  if (!withTagline) {
    return (
      <span className={className} title={`Domain: ${label}`}>
        {label}
      </span>
    );
  }
  return (
    <span className="domain-block">
      <span className={className} title={`Domain: ${label}`}>
        {label}
      </span>
      <span className="domain-tagline">{tagline}</span>
    </span>
  );
}
