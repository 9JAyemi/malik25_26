// SVA for counter_2bit
module counter_2bit_sva (
  input logic        CLK,
  input logic        RESET_B,
  input logic [1:0]  Q,
  input logic [1:0]  next_Q
);

  default clocking cb @(posedge CLK); endclocking

  // Async reset drives zero and holds zero while asserted
  assert property (@(negedge RESET_B) 1'b1 |=> (Q == 2'b00));
  assert property (cb !RESET_B |-> (Q == 2'b00));

  // No X/Z on Q once out of reset
  assert property (cb RESET_B |-> !$isunknown(Q));

  // Functional spec: count up mod-4 when out of reset on consecutive cycles
  assert property (cb RESET_B && $past(RESET_B) |-> (Q == ($past(Q) + 2'b01)));

  // Micro-arch check: next_Q must reflect (past) Q+1
  assert property (cb RESET_B && $past(RESET_B) |-> (next_Q == ($past(Q) + 2'b01)));

  // Micro-arch check: Q must follow current next_Q with wrap-to-zero
  assert property (cb RESET_B |-> (Q == ((next_Q == 2'b11) ? 2'b00 : next_Q)));

  // Coverage
  cover property (cb $rose(RESET_B));
  cover property (cb RESET_B && $past(RESET_B) ##1
                       (Q==2'b00) ##1 (Q==2'b01) ##1 (Q==2'b10) ##1 (Q==2'b11) ##1 (Q==2'b00));
  cover property (cb RESET_B && $past(RESET_B) && ($past(Q)==2'b11) ##1 (Q==2'b00));

endmodule

bind counter_2bit counter_2bit_sva sva(.CLK(CLK), .RESET_B(RESET_B), .Q(Q), .next_Q(next_Q));