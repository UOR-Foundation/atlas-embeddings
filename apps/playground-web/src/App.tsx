import React, { useState, useCallback, FC, PropsWithChildren } from 'react';
import { Atlas } from '@uor-foundation/sigmatics';
import type { Phrase, ClassInfo } from '@uor-foundation/sigmatics';

// Data for Docs component
const README_CONTENT = `A complete TypeScript implementation of the **Atlas Sigil Algebra** formal specification v1.0 - a symbolic computation system built on 7 fundamental generators and a 96-class resonance structure (≡₉₆).`;
const QUICKSTART_CONTENT = `
1. Type or paste an Atlas expression into the text area.
2. Click one of the example buttons to load a sample expression.
3. Click "Evaluate" to see the results.
4. Explore the Class System and Belt Address tools on the right.

**Sigil Grammar:**
<phrase>     ::= [ <transform> "@" ] <par>
<par>        ::= <seq> { "||" <seq> }
<seq>        ::= <term> { "." <term> }
<term>       ::= <op> | "(" <par> ")"
<op>         ::= <generator> "@" <sigil>
<sigil>      ::= "c" <0..95> ["^" ("+"|"-") <k>] ["~"] ["@" <λ:0..47>]
<transform>  ::= [ "R" ("+"|"-") <q> ] [ "D" ("+"|"-") <k> ] [ "T" ("+"|"-") <k> ] [ "~" ]
`;

// --- UI Components ---

const Card: FC<PropsWithChildren<{ title: string }>> = ({ title, children }) => (
  <div className="card">
    <h2>{title}</h2>
    {children}
  </div>
);

const Tabs: FC<PropsWithChildren<{ activeTab: string; onTabClick: (id: string) => void }>> = ({
  activeTab,
  onTabClick,
  children,
}) => {
  const tabs = React.Children.map(children, (child) => {
    if (React.isValidElement(child)) {
      return (
        <button
          className={`tab-button ${activeTab === child.props.id ? 'active' : ''}`}
          onClick={() => onTabClick(child.props.id)}
        >
          {child.props.label}
        </button>
      );
    }
    return null;
  });

  const activeContent = React.Children.toArray(children).find(
    (child) => React.isValidElement(child) && child.props.id === activeTab,
  );

  return (
    <div>
      <div className="tabs">{tabs}</div>
      <div className="tab-panel">{activeContent}</div>
    </div>
  );
};

const TabPanel: FC<PropsWithChildren<{ id: string; label: string }>> = ({ children }) => {
  return <>{children}</>;
};

// --- App Components ---

interface EvaluationResult {
  ast: Phrase;
  literal: { bytes: number[]; addresses?: number[] };
  operational: { words: string[] };
  pretty: string;
}

const ResultsComponent: FC<{ result: EvaluationResult | null; error: string | null }> = ({
  result,
  error,
}) => {
  const [activeTab, setActiveTab] = useState('summary');

  if (error) {
    return <pre className="error">{error}</pre>;
  }
  if (!result) {
    return <p>Enter an expression and click "Evaluate" to see the results.</p>;
  }

  return (
    <Tabs activeTab={activeTab} onTabClick={setActiveTab}>
      <TabPanel id="summary" label="Summary">
        <h3>Literal Bytes</h3>
        <pre>
          {result.literal.bytes
            .map((b) => '0x' + b.toString(16).toUpperCase().padStart(2, '0'))
            .join(' ')}
        </pre>
        {result.literal.addresses && (
          <>
            <h3>Belt Addresses</h3>
            <pre>{result.literal.addresses.join(', ')}</pre>
          </>
        )}
      </TabPanel>
      <TabPanel id="operational" label="Operational Words">
        <pre>{result.operational.words.join('\n')}</pre>
      </TabPanel>
      <TabPanel id="ast" label="AST">
        <pre>{JSON.stringify(result.ast, null, 2)}</pre>
      </TabPanel>
    </Tabs>
  );
};

const ClassExplorerComponent = () => {
  const [byteInput, setByteInput] = useState('42');
  const [classInfo, setClassInfo] = useState<ClassInfo | null>(null);
  const [equivalenceClass, setEquivalenceClass] = useState<number[]>([]);

  const handleByteChange = (e: React.ChangeEvent<HTMLInputElement>) => {
    const input = e.target.value;
    setByteInput(input);
    try {
      const byteValue = parseInt(input, input.startsWith('0x') ? 16 : 10);
      if (!isNaN(byteValue) && byteValue >= 0 && byteValue <= 255) {
        const info = Atlas.classInfo(byteValue);
        setClassInfo(info);
        setEquivalenceClass(Atlas.equivalenceClass(info.classIndex));
      } else {
        setClassInfo(null);
      }
    } catch {
      setClassInfo(null);
    }
  };

  return (
    <Card title="Class Explorer">
      <div className="input-group">
        <label htmlFor="byte-input">Enter Byte (0-255 or 0x00-0xFF)</label>
        <input id="byte-input" value={byteInput} onChange={handleByteChange} />
      </div>
      {classInfo && (
        <div>
          <p>
            <strong>Class Index:</strong> {classInfo.classIndex}
          </p>
          <p>
            <strong>Canonical Byte:</strong> 0x{classInfo.canonicalByte.toString(16).toUpperCase()}
          </p>
          <p>
            <strong>Components:</strong> (h₂={classInfo.components.h2}, d={classInfo.components.d},
            ℓ={classInfo.components.l})
          </p>
          <strong>Equivalence Class ({equivalenceClass.length} members):</strong>
          <pre style={{ maxHeight: '150px', overflowY: 'auto' }}>
            {equivalenceClass
              .map((b) => `0x${b.toString(16).toUpperCase().padStart(2, '0')}`)
              .join(', ')}
          </pre>
        </div>
      )}
    </Card>
  );
};

const BeltCalculatorComponent = () => {
  const [page, setPage] = useState('17');
  const [byte, setByte] = useState('46'); // 0x2E
  const [address, setAddress] = useState<number | string>('');

  React.useEffect(() => {
    const p = parseInt(page);
    const b = parseInt(byte);
    if (!isNaN(p) && !isNaN(b) && p >= 0 && p <= 47 && b >= 0 && b <= 255) {
      try {
        setAddress(Atlas.beltAddress(p, b).address);
      } catch {
        setAddress('Invalid');
      }
    } else {
      setAddress('Invalid');
    }
  }, [page, byte]);

  return (
    <Card title="Belt Address Calculator">
      <div className="input-group">
        <label htmlFor="page-input">Page (0-47)</label>
        <input
          id="page-input"
          value={page}
          onChange={(e) => setPage(e.target.value)}
          type="number"
          min="0"
          max="47"
        />
      </div>
      <div className="input-group">
        <label htmlFor="byte-calc-input">Byte (0-255)</label>
        <input
          id="byte-calc-input"
          value={byte}
          onChange={(e) => setByte(e.target.value)}
          type="number"
          min="0"
          max="255"
        />
      </div>
      <strong>Address:</strong>
      <pre>{address}</pre>
    </Card>
  );
};

const DocsComponent = () => (
  <details>
    <summary>Documentation</summary>
    <Card title="About Atlas">
      <p>{README_CONTENT}</p>
    </Card>
    <Card title="Quick Start">
      <pre>{QUICKSTART_CONTENT}</pre>
    </Card>
  </details>
);

const App = () => {
  const [expression, setExpression] = useState('evaluate@c21 . copy@c05');
  const [result, setResult] = useState<EvaluationResult | null>(null);
  const [error, setError] = useState<string | null>(null);

  const handleEvaluate = useCallback(() => {
    setError(null);
    if (!expression.trim()) {
      setResult(null);
      return;
    }
    try {
      const evaluation = Atlas.evaluate(expression);
      setResult({
        ...evaluation,
        pretty: Atlas.prettyPrint(expression),
      });
    } catch (e: any) {
      setError(e.message);
      setResult(null);
    }
  }, [expression]);

  const EXAMPLES = [
    'mark@c21',
    'evaluate@c21 . copy@c05 || swap@c72',
    'R+1@ (copy@c05 . evaluate@c21)',
    'mark@c42^+3~@17',
  ];

  return (
    <>
      <header className="container">
        <h1>Atlas Sigil Algebra Playground</h1>
        <p>An interactive environment for the Atlas symbolic computation system</p>
      </header>
      <main className="container main-content">
        <div className="evaluator-column">
          <Card title="Expression Evaluator">
            <textarea
              value={expression}
              onChange={(e) => setExpression(e.target.value)}
              placeholder="Enter Atlas expression here..."
              aria-label="Atlas Expression Input"
            />
            <div style={{ marginTop: '1rem', display: 'flex', alignItems: 'center', gap: '1rem' }}>
              <button className="button" onClick={handleEvaluate}>
                Evaluate
              </button>
              <div className="example-buttons">
                {EXAMPLES.map((ex) => (
                  <button key={ex} className="example-button" onClick={() => setExpression(ex)}>
                    {ex}
                  </button>
                ))}
              </div>
            </div>
          </Card>
          <Card title="Results">
            <ResultsComponent result={result} error={error} />
          </Card>
        </div>
        <div className="tools-column">
          <ClassExplorerComponent />
          <BeltCalculatorComponent />
          <DocsComponent />
        </div>
      </main>
    </>
  );
};

export default App;
