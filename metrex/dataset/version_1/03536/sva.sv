// SVA for and_en — concise, high-quality checks and coverage
module and_en_sva (
  input logic [2:0] a, b, c,
  input logic       en,
  input logic       y,
  input logic [2:0] and_result
);
  // Local helpers
  let b0   = a[0] & b[0] & c[0];
  let b1   = a[1] & b[1] & c[1];
  let b2   = a[2] & b[2] & c[2];
  let all3 = b0 & b1 & b2;

  // Functional equivalence (guarded against X/Z on inputs)
  assert property (@(*)) (!$isunknown({a,b,c,en})) |-> (y === (en & all3));

  // Internal bitwise AND is correct (guarded)
  assert property (@(*)) (!$isunknown({a,b,c})) |-> (and_result === (a & b & c));

  // Enable gating correctness
  assert property (@(*)) !en |-> (y === 1'b0);
  assert property (@(*)) en  |-> (y === all3);

  // Necessity: y implies en and all contributing bits are 1
  assert property (@(*)) y |-> (en && b0 && b1 && b2);

  // No unknown on output when inputs are known
  assert property (@(*)) (!$isunknown({a,b,c,en})) |-> !$isunknown(y);

  // Coverage: hit all key functional scenarios
  cover property (@(*))  en &&  b0 &&  b1 &&  b2 &&  y;   // y=1 path
  cover property (@(*))  en && !b0 &&  b1 &&  b2 && !y;   // bit0 kills y
  cover property (@(*))  en &&  b0 && !b1 &&  b2 && !y;   // bit1 kills y
  cover property (@(*))  en &&  b0 &&  b1 && !b2 && !y;   // bit2 kills y
  cover property (@(*)) !en && (b0 || b1 || b2) && !y;    // gating forces 0 despite some ones
  cover property (@(*)) !en && !(b0 || b1 || b2) && !y;   // all zeros with en=0
endmodule

// Bind into the DUT (gives access to internal and_result)
bind and_en and_en_sva sva_i(.*);