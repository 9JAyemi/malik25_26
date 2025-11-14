// Bindable SVA checker for MUX41X1
module MUX41X1_sva (
  input logic IN1,IN2,IN3,IN4,
  input logic S0,S1,
  input logic Q,
  input logic t1,t2
);

  // Functional correctness (4-state exact)
  always @* begin
    assert (t1 === (S1 ? IN1 : IN2)) else $error("t1 mismatch");
    assert (t2 === (S1 ? IN3 : IN4)) else $error("t2 mismatch");
    assert (Q  === (S0 ? t1 : t2))   else $error("Q vs t1/t2 mismatch");
    assert (Q  === (S0 ? (S1 ? IN1 : IN2) : (S1 ? IN3 : IN4)))
      else $error("Q direct expr mismatch");
  end

  // Zero-delay propagation on data/input control changes
  assert property (@(posedge IN1 or negedge IN1) S0 &&  S1 && !$isunknown({S0,S1,IN1}) |-> ##0 (Q === IN1));
  assert property (@(posedge IN2 or negedge IN2) S0 && !S1 && !$isunknown({S0,S1,IN2}) |-> ##0 (Q === IN2));
  assert property (@(posedge IN3 or negedge IN3) !S0 &&  S1 && !$isunknown({S0,S1,IN3}) |-> ##0 (Q === IN3));
  assert property (@(posedge IN4 or negedge IN4) !S0 && !S1 && !$isunknown({S0,S1,IN4}) |-> ##0 (Q === IN4));

  assert property (@(posedge S0 or negedge S0) !$isunknown({S0,t1,t2}) |-> ##0 (Q === (S0 ? t1 : t2)));
  assert property (@(posedge S1 or negedge S1) !$isunknown({S1,IN1,IN2,IN3,IN4})
                   |-> ##0 (t1 === (S1 ? IN1 : IN2) && t2 === (S1 ? IN3 : IN4)));

  // Sanity: when selects and selected input are known, Q must be known
  always @* if (!$isunknown({S0,S1})) begin
    unique case ({S0,S1})
      2'b11: if (!$isunknown(IN1)) assert (!$isunknown(Q)) else ;
      2'b10: if (!$isunknown(IN2)) assert (!$isunknown(Q)) else ;
      2'b01: if (!$isunknown(IN3)) assert (!$isunknown(Q)) else ;
      2'b00: if (!$isunknown(IN4)) assert (!$isunknown(Q)) else ;
    endcase
  end

  // Coverage
  always @* begin
    cover ({S0,S1} == 2'b00);
    cover ({S0,S1} == 2'b01);
    cover ({S0,S1} == 2'b10);
    cover ({S0,S1} == 2'b11);
  end

  cover property (@(posedge IN1 or negedge IN1) S0 &&  S1 && !$isunknown({S0,S1,IN1}) ##0 (Q === IN1));
  cover property (@(posedge IN2 or negedge IN2) S0 && !S1 && !$isunknown({S0,S1,IN2}) ##0 (Q === IN2));
  cover property (@(posedge IN3 or negedge IN3) !S0 &&  S1 && !$isunknown({S0,S1,IN3}) ##0 (Q === IN3));
  cover property (@(posedge IN4 or negedge IN4) !S0 && !S1 && !$isunknown({S0,S1,IN4}) ##0 (Q === IN4));

  cover property (@(posedge S0 or negedge S0) !$isunknown({S0,t1,t2}) ##0 (Q === (S0 ? t1 : t2)));

endmodule

// Bind into the DUT (connects to internal nets t1/t2)
bind MUX41X1 MUX41X1_sva sva (
  .IN1(IN1), .IN2(IN2), .IN3(IN3), .IN4(IN4),
  .S0(S0), .S1(S1),
  .Q(Q),
  .t1(t1), .t2(t2)
);