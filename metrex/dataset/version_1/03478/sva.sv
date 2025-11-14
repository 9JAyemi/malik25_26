// SVA for johnson_counter
// Focus: functional next-state relation, shift behavior, X-propagation, out mirroring, concise coverage.

module johnson_counter_sva #(
  parameter int n = 16
)(
  input  logic              clk,
  input  logic [n-1:0]      out,
  input  logic [n-1:0]      state
);

  // Elaboration-time sanity
  initial begin
    if (n < 2) $error("johnson_counter: n must be >= 2 (uses state[n-2])");
  end

  default clocking cb @(posedge clk); endclocking

  // Helper: only check once a valid past sample exists
  function automatic bit past_valid();
    return !$isunknown($past(state));
  endfunction

  // out mirrors state
  a_out_mirrors_state: assert property (out == state)
    else $error("out != state");

  // No Xs after first valid cycle
  a_no_x: assert property (past_valid() |-> (! $isunknown(state) && ! $isunknown(out)))
    else $error("X/Z detected on state/out");

  // Shift behavior for bits [n-1:1]: state[i] <- $past(state[i-1])
  genvar i;
  generate
    for (i = 1; i < n; i++) begin : g_shift
      a_shift: assert property (past_valid() |-> state[i] == $past(state[i-1]))
        else $error("Shift mismatch at bit %0d", i);
    end
  endgenerate

  // LSB feedback: state[0] <- ~$past(state[n-1]) ^ $past(state[n-2])
  a_feedback: assert property (
      !$isunknown($past(state[n-1:n-2])) |-> state[0] == ((~$past(state[n-1])) ^ $past(state[n-2]))
    ) else $error("Feedback mismatch at LSB");

  // Optional: full next-state check (redundant with above but concise)
  a_whole_vector: assert property (
      past_valid() |-> state == { $past(state[n-2:0]), ((~$past(state[n-1])) ^ $past(state[n-2])) }
    ) else $error("Vector next-state mismatch");

  // Concise functional coverage
  // - Observe both edges on LSB and MSB
  c_lsb_rise: cover property ($rose(state[0]));
  c_lsb_fall: cover property ($fell(state[0]));
  c_msb_rise: cover property ($rose(state[n-1]));
  c_msb_fall: cover property ($fell(state[n-1]));

  // - Observe a '1' bit propagating through the shift path
  generate
    for (i = 1; i < n; i++) begin : g_cover_shift1
      c_shift1: cover property (state[i-1] ##1 state[i]);
    end
  endgenerate

  // - Observe a potential cycle closure at 2*n steps (typical Johnson length; recorded as coverage only)
  c_period_2n: cover property (state == $past(state, 2*n));

endmodule

// Bind into the DUT (allows access to internal 'state')
bind johnson_counter
  johnson_counter_sva #(.n(n)) u_johnson_counter_sva (
    .clk  (clk),
    .out  (out),
    .state(state)
  );