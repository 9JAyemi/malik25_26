// SVA checker for up_down_counter
module up_down_counter_sva (
  input logic        CLK,
  input logic        LOAD,
  input logic [2:0]  LOAD_VAL,
  input logic        UP_DOWN,
  input logic        CARRY_IN,
  input logic [2:0]  Q,
  input logic [2:0]  Q_reg1,
  input logic [2:0]  Q_reg2,
  input logic [2:0]  Q_reg3
);

  // clocking and past-valid
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge CLK) past_valid <= 1'b1;

  default clocking cb @(posedge CLK); endclocking

  // Basic X checks
  assert property ( !$isunknown({LOAD, UP_DOWN, CARRY_IN}) )
    else $error("X/Z on control inputs");
  assert property ( LOAD |-> !$isunknown(LOAD_VAL) )
    else $error("X/Z on LOAD_VAL when LOAD=1");
  assert property ( !$isunknown(Q) )
    else $error("X/Z on Q");

  // Pipeline/retiming correctness
  assert property ( past_valid |-> (Q_reg1 == $past(Q)) )
    else $error("Q_reg1 must equal prior Q");
  assert property ( past_valid |-> (Q_reg2 == $past(Q_reg1)) )
    else $error("Q_reg2 must equal prior Q_reg1");
  assert property ( past_valid |-> (Q_reg3 == $past(Q_reg2)) )
    else $error("Q_reg3 must equal prior Q_reg2");

  // Next-state function
  // LOAD has priority
  assert property ( past_valid && LOAD |=> (Q == $past(LOAD_VAL)) )
    else $error("LOAD next-state mismatch");
  // Count up/down using one-cycle-delayed Q
  assert property ( past_valid && !LOAD && UP_DOWN |=> (Q == $past(Q) + $past(CARRY_IN)) )
    else $error("UP next-state mismatch");
  assert property ( past_valid && !LOAD && !UP_DOWN |=> (Q == $past(Q) - $past(CARRY_IN)) )
    else $error("DOWN next-state mismatch");

  // Functional coverage
  cover property ( LOAD ##1 (Q == $past(LOAD_VAL)) );
  cover property ( !LOAD && UP_DOWN && CARRY_IN ##1 (Q == $past(Q) + 1) );
  cover property ( !LOAD && !UP_DOWN && CARRY_IN ##1 (Q == $past(Q) - 1) );
  cover property ( !LOAD && (CARRY_IN == 1'b0) ##1 (Q == $past(Q)) );
  // Wrap-around coverage
  cover property ( !LOAD && UP_DOWN && CARRY_IN && (Q == 3'b111) ##1 (Q == 3'b000) );
  cover property ( !LOAD && !UP_DOWN && CARRY_IN && (Q == 3'b000) ##1 (Q == 3'b111) );
  // Retiming chain observation
  cover property ( past_valid ##3 (Q_reg3 == $past(Q,3)) );

endmodule

// Bind the checker to the DUT, including internal regs
bind up_down_counter up_down_counter_sva sva_u (
  .CLK(CLK),
  .LOAD(LOAD),
  .LOAD_VAL(LOAD_VAL),
  .UP_DOWN(UP_DOWN),
  .CARRY_IN(CARRY_IN),
  .Q(Q),
  .Q_reg1(Q_reg1),
  .Q_reg2(Q_reg2),
  .Q_reg3(Q_reg3)
);