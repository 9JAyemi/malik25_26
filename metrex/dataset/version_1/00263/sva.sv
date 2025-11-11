// SVA for FSM_Ctrol
module FSM_Ctrol_sva (
  input logic              RST,
  input logic              CLK,
  input logic              STM,
  input logic [7:0]        ENa, ENb, ENc, SEL,
  input logic              EOM,
  input logic [2:0]        Qp, Qn
);

  default clocking cb @(posedge CLK); endclocking
  default disable iff (RST);

  bit past_valid;
  always_ff @(posedge CLK or posedge RST) begin
    if (RST) past_valid <= 1'b0;
    else     past_valid <= 1'b1;
  end

  // Legal encodings
  assert property (Qp inside {3'd0,3'd1,3'd2,3'd3,3'd4});
  assert property (Qn inside {3'd0,3'd1,3'd2,3'd3,3'd4});

  // Async reset behavior
  assert property (@(posedge RST) 1'b1 |-> (Qp==3'd0));
  assert property (RST |-> (Qp==3'd0));

  // Next-state combinational map
  assert property ((Qp==3'd0) |-> (Qn == (STM ? 3'd1 : 3'd0)));
  assert property ((Qp==3'd1) |-> (Qn == 3'd2));
  assert property ((Qp==3'd2) |-> (Qn == 3'd3));
  assert property ((Qp==3'd3) |-> (Qn == 3'd4));
  assert property ((Qp==3'd4) |-> (Qn == 3'd0));

  // Registered update
  assert property (past_valid |-> (Qp == $past(Qn)));

  // Output decode per state
  assert property ((Qp==3'd0) |-> (ENa==8'b00001111 && ENb==8'b00001111 && ENc==8'b00000000 && SEL==8'b00000000 && EOM==1'b1));
  assert property ((Qp==3'd1) |-> (ENa==8'b11110000 && ENb==8'b11110000 && ENc==8'b00000000 && SEL==8'b00000000 && EOM==1'b0));
  assert property ((Qp==3'd2) |-> (ENa==8'b01011010 && ENb==8'b00000000 && ENc==8'b00000000 && SEL==8'b10010101 && EOM==1'b0));
  assert property ((Qp==3'd3) |-> (ENa==8'b00000000 && ENb==8'b00111100 && ENc==8'b00000000 && SEL==8'b01101010 && EOM==1'b0));
  assert property ((Qp==3'd4) |-> (ENa==8'b00000000 && ENb==8'b00000000 && ENc==8'b11111111 && SEL==8'b01101010 && EOM==1'b0));

  // EOM only in state 0
  assert property (EOM |-> (Qp==3'd0));

  // Outputs only change when state changes
  assert property ($changed({ENa,ENb,ENc,SEL,EOM}) |-> $changed(Qp));

  // No X/Z when not in reset
  assert property (!$isunknown({Qp,Qn,ENa,ENb,ENc,SEL,EOM}));

  // Coverage
  cover property (Qp==3'd0);
  cover property (Qp==3'd1);
  cover property (Qp==3'd2);
  cover property (Qp==3'd3);
  cover property (Qp==3'd4);

  cover property ((Qp==3'd0 && !STM) ##1 (Qp==3'd0)); // idle hold
  cover property ((Qp==3'd0 && STM) ##1 (Qp==3'd1) ##1 (Qp==3'd2) ##1 (Qp==3'd3) ##1 (Qp==3'd4) ##1 (Qp==3'd0)); // full cycle

endmodule

bind FSM_Ctrol FSM_Ctrol_sva sva_inst (.*);