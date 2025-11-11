// SVA checker for binary_counter
module binary_counter_sva #(parameter WIDTH=4) (
  input  logic              CLK,
  input  logic              RST,
  input  logic              COUNT_EN,
  input  logic [WIDTH-1:0]  Q
);

  default clocking cb @(posedge CLK); endclocking

  // Reset behavior
  a_rst_clears_next: assert property (RST |=> (Q == '0));
  a_rst_holds_stable: assert property ((RST && $past(RST)) |-> $stable(Q));

  // Q must never be X/Z once out of reset
  a_q_known: assert property (disable iff (RST) !$isunknown(Q));

  // Counting rules (outside reset)
  a_inc_when_en:   assert property (disable iff (RST) COUNT_EN   |=> (Q == $past(Q) + 1'b1));
  a_hold_when_dis: assert property (disable iff (RST) !COUNT_EN  |=> (Q == $past(Q)));

  // Explicit wrap-around check
  a_wrap: assert property (disable iff (RST) (Q == {WIDTH{1'b1}} && COUNT_EN) |=> (Q == '0));

  // Coverage
  c_reset:    cover property (RST ##1 (Q == '0));
  c_increment: cover property (disable iff (RST) COUNT_EN ##1 (Q == $past(Q) + 1'b1));
  c_hold:     cover property (disable iff (RST) !COUNT_EN ##1 (Q == $past(Q)));
  c_wrap:     cover property (disable iff (RST) (Q == {WIDTH{1'b1}} && COUNT_EN) ##1 (Q == '0));
  c_full_cycle: cover property (RST ##1 (!RST && COUNT_EN) [*16] ##1 (Q == '0));

endmodule

// Bind into DUT
bind binary_counter binary_counter_sva #(.WIDTH(4)) u_binary_counter_sva (
  .CLK(CLK), .RST(RST), .COUNT_EN(COUNT_EN), .Q(Q)
);