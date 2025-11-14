// SVA checker for adder_subtractor_4bit
// Concise, high-value functional checks + key coverage.
// Uses event-based clocking and ##0 to allow combinational NBA settle.

module adder_subtractor_4bit_sva
(
  input logic [3:0] a,
  input logic [3:0] b,
  input logic       sub,
  input logic [3:0] sum
);

  // Functional correctness (modulo-16) after 0-delay settle
  property p_addsub_correct;
    @(a or b or sub)
      (!$isunknown({a,b,sub})) |-> ##0 (sum == (sub ? (a - b) : (a + b)));
  endproperty
  assert property (p_addsub_correct);

  // Output must be known when inputs are known
  property p_sum_known_when_inputs_known;
    @(a or b or sub)
      (!$isunknown({a,b,sub})) |-> ##0 (!$isunknown(sum));
  endproperty
  assert property (p_sum_known_when_inputs_known);

  // No output change without an input change (combinational, no hidden state/glitch)
  property p_no_spurious_sum_change;
    @(a or b or sub or sum)
      (!$changed({a,b,sub})) |-> (!$changed(sum));
  endproperty
  assert property (p_no_spurious_sum_change);

  // Basic mode coverage
  cover property (@(a or b or sub) !sub ##0 (sum == (a + b)));
  cover property (@(a or b or sub)  sub ##0 (sum == (a - b)));

  // Corner/interesting scenarios
  // Addition overflow (wrap)
  cover property (@(a or b or sub) !sub && ((a + b) < a));
  // Subtraction borrow
  cover property (@(a or b or sub)  sub && (a < b));
  // Zero result
  cover property (@(a or b or sub) ##0 (sum == 4'h0));
  // Max result
  cover property (@(a or b or sub) ##0 (sum == 4'hF));
  // Subtract equal operands -> zero
  cover property (@(a or b or sub)  sub && (a == b) ##0 (sum == 4'h0));
  // Add with zero operands
  cover property (@(a or b or sub) !sub && (a == 4'h0) && (b == 4'h0));
  // Exercise unknowns on inputs (for X-prop exploration)
  cover property (@(a or b or sub) $isunknown({a,b,sub}));

endmodule

// Bind into DUT
bind adder_subtractor_4bit adder_subtractor_4bit_sva sva_i(.a(a), .b(b), .sub(sub), .sum(sum));