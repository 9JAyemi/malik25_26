// SystemVerilog Assertions for dff_async_set_reset
`ifndef SYNTHESIS
module dff_async_set_reset_sva (
  input logic D,
  input logic SET_B,
  input logic RESET_B,
  input logic CLK,
  input logic Q,
  input logic Q_B
);

  default clocking cb @(posedge CLK); endclocking

  // Functional correctness per clock edge (priority: reset > set > data)
  assert property (!RESET_B |-> ##0 (Q==1'b0 && Q_B==1'b1));
  assert property ( RESET_B && !SET_B |-> ##0 (Q==1'b1 && Q_B==1'b0));
  assert property ( RESET_B &&  SET_B && !$isunknown(D) |-> ##0 (Q==D && Q_B==~D));

  // Outputs are always complementary after update (tolerates X via ===)
  assert property (1'b1 |-> ##0 (Q_B === ~Q));

  // Outputs only change on CLK rising edge
  assert property (@(posedge $global_clock) $rose(CLK) or !$changed({Q,Q_B}));

  // Known outputs when any control is asserted
  assert property ((!RESET_B || !SET_B) |-> ##0 !$isunknown({Q,Q_B}));

  // Coverage: exercise all modes and priority
  cover property (!RESET_B                       ##0 (Q==1'b0 && Q_B==1'b1));
  cover property ( RESET_B && !SET_B             ##0 (Q==1'b1 && Q_B==1'b0));
  cover property ( RESET_B &&  SET_B && D==1'b0  ##0 (Q==1'b0 && Q_B==1'b1));
  cover property ( RESET_B &&  SET_B && D==1'b1  ##0 (Q==1'b1 && Q_B==1'b0));
  cover property (!RESET_B && !SET_B             ##0 (Q==1'b0 && Q_B==1'b1)); // reset wins

endmodule

bind dff_async_set_reset dff_async_set_reset_sva sva_i (.*);
`endif