// SystemVerilog Assertions for the provided design
// Concise, quality-focused checks and coverage

// Bind into top_module; uses its clk for sampling
module top_sva (
  input logic        clk,
  input logic        reset,
  input logic        up_down,
  input logic [3:0]  A,
  input logic [1:0]  B,
  input logic [3:0]  Q,
  input logic        COUT,
  input logic [3:0]  count,
  input logic [7:0]  sum
);
  default clocking cb @ (posedge clk); endclocking

  // ----------------------
  // Barrel shifter checks
  // ----------------------
  // Functional Q mapping
  assert property (B[1] |-> Q == {A[3], A[3:1]});
  assert property (!B[1] && B[0] |-> Q == {A[2:0], A[3]});
  assert property (!B[1] && !B[0] |-> Q == A);

  // COUT behavior (case-wise, independent of Q)
  assert property (B == 2'b00 |-> COUT == 1'b0);
  assert property (B[1]              |-> COUT == A[1]);
  assert property (!B[1] && B[0]     |-> COUT == A[3]);

  // Optional consistency with spec equation
  assert property (COUT == Q[0] & (B[1] | B[0]));

  // Coverage of all shift modes and COUT outcomes
  cover property (B == 2'b00 && Q == A && COUT == 0);
  cover property (B[1] && Q == {A[3],A[3:1]} && COUT == A[1]);
  cover property (!B[1] && B[0] && Q == {A[2:0],A[3]} && COUT == A[3]);
  cover property (B[1] && A[1]);                 // COUT=1 in B[1] path
  cover property (!B[1] && B[0] && A[3]);        // COUT=1 in B[0]-only path

  // ----------------------
  // Up/down counter checks
  // ----------------------
  // Reset drives count to 0 on next cycle
  assert property (reset |-> count == 4'h0);

  // Count up/down relative to previous cycle; guard past with previous !reset
  assert property (disable iff (reset)
                   $past(!reset) && up_down |-> count == $past(count) + 1);
  assert property (disable iff (reset)
                   $past(!reset) && !up_down |-> count == $past(count) - 1);

  // Wrap-around coverage
  cover property (disable iff (reset)
                  $past(!reset) && up_down && $past(count)==4'hF && count==4'h0);
  cover property (disable iff (reset)
                  $past(!reset) && !up_down && $past(count)==4'h0 && count==4'hF);

  // Toggle direction coverage
  cover property (disable iff (reset)
                  $past(!reset) && $past(up_down) && !up_down);
  cover property (disable iff (reset)
                  $past(!reset) && !$past(up_down) && up_down);

  // ----------------------
  // Functional module/top wiring checks
  // ----------------------
  assert property (sum == {Q, count});
  cover property (Q==4'h0 && count==4'h0 && sum==8'h00);
  cover property (Q==4'hF && count==4'hF && sum==8'hFF);

  // ----------------------
  // Basic X-propagation sanity (when inputs are known)
  // ----------------------
  assert property (!$isunknown({A,B}) |-> !$isunknown({Q,COUT}));
  assert property (disable iff (reset) !$isunknown(up_down) |-> !$isunknown(count));

endmodule

bind top_module top_sva u_top_sva (.*);