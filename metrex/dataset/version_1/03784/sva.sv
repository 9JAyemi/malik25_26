// SVA checker for johnson_counter.
// Binds into the DUT, re-computes expected next state, and checks update/outputs.
// Concise but covers key behavior and provides useful coverage.

module johnson_counter_sva #(
  parameter int n = 4
)(
  input  logic               clock,
  input  logic [n-1:0]       out,
  input  logic [n-1:0]       shift_reg,
  input  logic [n-1:0]       next_state
);

  // Parameter sanity
  initial begin
    if (n < 3) $error("johnson_counter: n must be >= 3 (uses n-3 indexing).");
  end

  // calc_next: same rule as DUT, but as a pure function
  function automatic logic [n-1:0] calc_next (input logic [n-1:0] s);
    logic [n-1:0] ns;
    begin
      ns[0]      = s[n-1] ^ s[n-2];
      ns[n-1]    = s[n-2] ^ s[n-3];
      for (int i = 1; i < n-1; i++) begin
        ns[i] = s[i-1] ^ s[i] ^ s[i+1];
      end
      return ns;
    end
  endfunction

  // Track past-valid
  bit past_valid;
  initial past_valid = 0;
  always @(posedge clock) past_valid <= 1;

  // 1) Combinational next_state matches rule (when inputs are known)
  assert property (@(posedge clock) !$isunknown(shift_reg) |-> (next_state == calc_next(shift_reg)))
    else $error("next_state does not match combinational rule");

  // 2) Sequential update: state at t equals calc_next(prev_state) at t-1
  assert property (@(posedge clock)
                   past_valid && !$isunknown($past(shift_reg))
                   |-> (shift_reg == calc_next($past(shift_reg))))
    else $error("Sequential update mismatch: shift_reg != calc_next($past(shift_reg))");

  // 3) Output mirrors state (allowing X/Z equality)
  assert property (@(posedge clock) (out === shift_reg))
    else $error("out must continuously mirror shift_reg");

  // 4) No async glitches on state (stable between clock edges)
  assert property (@(negedge clock) $stable(shift_reg))
    else $error("shift_reg changed outside posedge clock");

  // 5) If state changes on a clock, output changes the same cycle
  assert property (@(posedge clock) $changed(shift_reg) |-> $changed(out))
    else $error("out did not track shift_reg change");

  // 6) Cross-check: internal next_state actually feeds the flop on next edge
  assert property (@(posedge clock)
                   past_valid && !$isunknown($past(next_state))
                   |-> (shift_reg == $past(next_state)))
    else $error("shift_reg != $past(next_state)");

  // Coverage: observe useful activity
  genvar j;
  generate
    for (j = 0; j < n; j++) begin : COV_BITS
      cover property (@(posedge clock) $rose(out[j]));
      cover property (@(posedge clock) $fell(out[j]));
    end
  endgenerate

  // Cover that the state changes for several consecutive cycles (exercise dynamics)
  cover property (@(posedge clock) past_valid and $changed(out) [*4]);

  // Cover a state repeat (some cycle detected within a modest window)
  // Window kept small for practicality; adjust as needed.
  cover property (@(posedge clock) past_valid ##[1:n+4] (out == $past(out)));

endmodule

// Bind into the DUT (exposes internal shift_reg and next_state)
bind johnson_counter
  johnson_counter_sva #(.n(n)) i_johnson_counter_sva (
    .clock      (clock),
    .out        (out),
    .shift_reg  (shift_reg),
    .next_state (next_state)
  );