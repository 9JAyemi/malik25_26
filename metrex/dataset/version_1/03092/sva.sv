// SVA for binary_counter
module binary_counter_sva (
  input logic        iCLK,
  input logic        iRST,
  input logic [3:0]  oCOUNT
);

  default clocking cb @ (posedge iCLK); endclocking

  // past-valid helper
  logic past_valid;
  initial past_valid = 0;
  always @(posedge iCLK) past_valid <= 1;

  // X/Z checks
  a_no_x_inputs_outputs: assert property ( !$isunknown(iRST) && !$isunknown(oCOUNT) );

  // Reset behavior
  a_reset_zero:         assert property ( iRST |-> (oCOUNT == 4'h0) );
  a_reset_stable:       assert property ( past_valid && $past(iRST) && iRST |-> $stable(oCOUNT) );

  // Increment behavior (no reset)
  a_inc_no_reset:       assert property ( past_valid && !$past(iRST) && !iRST |-> oCOUNT == $past(oCOUNT) + 1 );

  // First cycle after reset deassertion also increments from 0
  a_inc_after_reset:    assert property ( past_valid && $past(iRST) && !iRST |-> oCOUNT == $past(oCOUNT) + 1 );

  // Explicit wrap check
  a_wrap_15_to_0:       assert property ( past_valid && !$past(iRST) && !iRST && $past(oCOUNT) == 4'hF |-> oCOUNT == 4'h0 );

  // Coverage
  c_seen_reset:         cover  property ( iRST );
  c_0_to_1:             cover  property ( past_valid && !$past(iRST) && !iRST && $past(oCOUNT)==4'h0 && oCOUNT==4'h1 );
  c_wrap_15_to_0:       cover  property ( past_valid && !$past(iRST) && !iRST && $past(oCOUNT)==4'hF && oCOUNT==4'h0 );
  c_full_cycle:         cover  property ( (!iRST && oCOUNT==4'h0) ##1 (!iRST)[*14] ##1 (!iRST && oCOUNT==4'hF) ##1 (!iRST && oCOUNT==4'h0) );

endmodule

// Bind into DUT
bind binary_counter binary_counter_sva u_binary_counter_sva (
  .iCLK(iCLK),
  .iRST(iRST),
  .oCOUNT(oCOUNT)
);