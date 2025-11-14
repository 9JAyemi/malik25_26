// SVA for GrayCodeStateMachine
// Bindable checker; verifies correctness, single-bit Gray transitions, incrementing counter, no Xs, and key coverage.

module graycode_sva #(parameter int n = 4)
(
  input logic                  clk,
  input logic [n-1:0]          state,
  input logic [n-1:0]          currentState
);

  // local utilities
  function automatic [n-1:0] gray_enc(input [n-1:0] bin);
    gray_enc = bin ^ (bin >> 1);
  endfunction

  function automatic [n-1:0] gray_dec(input [n-1:0] g);
    automatic logic [n-1:0] b;
    int j;
    b[n-1] = g[n-1];
    for (j = n-2; j >= 0; j--) b[j] = b[j+1] ^ g[j];
    gray_dec = b;
  endfunction

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Parameter sanity
  initial assert (n > 0) else $error("n must be > 0");

  // No X/Z on key state signals at sampling
  assert property (!($isunknown(state) || $isunknown(currentState)))
    else $error("X/Z detected on state/currentState");

  // Functional consistency: output is Gray encoding of currentState
  assert property (state == gray_enc(currentState))
    else $error("state != gray_enc(currentState): state=%0h curr=%0h", state, currentState);

  // Optional inverse check: decoding state yields currentState
  assert property (gray_dec(state) == currentState)
    else $error("gray_dec(state) != currentState: state=%0h curr=%0h", state, currentState);

  // currentState increments by 1 every cycle (wraps modulo 2^n)
  assert property (past_valid |-> currentState == $past(currentState) + 1)
    else $error("currentState did not increment by 1: past=%0h curr=%0h", $past(currentState), currentState);

  // Gray code property: exactly one bit toggles each cycle on state
  assert property (past_valid |-> $countones(state ^ $past(state)) == 1)
    else $error("Non-Gray transition: %0h -> %0h (diff=%0h)", $past(state), state, (state ^ $past(state)));

  // Coverage: see a full cycle (wrap after 2^n steps)
  cover property (past_valid && currentState == '0 ##(2**n) currentState == '0);

  // Coverage: observe wrap-around boundary
  cover property (past_valid && $past(currentState) == {n{1'b1}} && currentState == '0);

  // Coverage: every bit toggles at least once
  genvar i;
  generate
    for (i = 0; i < n; i++) begin : bit_toggle_cov
      cover property ($changed(state[i]));
    end
  endgenerate

endmodule

// Bind into the DUT (tool supports binding to internal signals)
bind GrayCodeStateMachine graycode_sva #(.n(n))
  u_graycode_sva (.clk(clk), .state(state), .currentState(currentState));