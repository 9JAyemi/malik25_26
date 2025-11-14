// SVA for flip_flop
// Bind into DUT: bind flip_flop flip_flop_sva i_flip_flop_sva(.*);

module flip_flop_sva (
  input logic CLK,
  input logic D,
  input logic SET_B,
  input logic CLR_B,
  input logic Q,
  input logic Q_N
);

  // establish clock/past-valid
  default clocking cb @(posedge CLK); endclocking
  bit past_valid;
  always_ff @(posedge CLK) past_valid <= 1'b1;

  // Disable checks until first clock and when inputs are X
  `define DISABLE (!past_valid || $isunknown({SET_B,CLR_B,D}))

  // Functional priority and behavior
  // SET has highest priority
  assert property (disable iff (`DISABLE)
                   (!SET_B) |-> ##0 (Q == 1'b1 && Q_N == 1'b0));

  // CLR takes effect only if SET not asserted
  assert property (disable iff (`DISABLE)
                   (SET_B && !CLR_B) |-> ##0 (Q == 1'b0 && Q_N == 1'b1));

  // Data path when both inactive (sample previous-cycle D)
  assert property (disable iff (`DISABLE)
                   (SET_B && CLR_B) |-> ##0 (Q == $past(D) && Q_N == ~$past(D)));

  // Outputs are always complements (after update)
  assert property (disable iff (!past_valid)
                   1'b1 |-> ##0 (Q_N == ~Q));

  // Outputs do not glitch: only change on CLK rising edge
  assert property (disable iff (!past_valid) $changed(Q)   |-> $rose(CLK));
  assert property (disable iff (!past_valid) $changed(Q_N) |-> $rose(CLK));

  // No X on outputs when inputs known
  assert property (disable iff (`DISABLE) ##0 !$isunknown({Q,Q_N}));

  // Coverage: exercise all branches and data toggles
  cover property (!SET_B |-> ##0 (Q && !Q_N));                      // SET
  cover property (SET_B && !CLR_B |-> ##0 (!Q && Q_N));             // CLR
  cover property (SET_B && CLR_B && $past(Q)==0 && $past(D)==1
                  |-> ##0 (Q==1 && Q_N==0));                        // data 0->1
  cover property (SET_B && CLR_B && $past(Q)==1 && $past(D)==0
                  |-> ##0 (Q==0 && Q_N==1));                        // data 1->0
  cover property (!SET_B && !CLR_B |-> ##0 (Q && !Q_N));            // both asserted -> SET wins

  `undef DISABLE
endmodule