// SVA for binary_counter
module binary_counter_sva (
  input logic       CLK,
  input logic       RST,      // synchronous, active-high
  input logic [3:0] Q
);
  default clocking cb @(posedge CLK); endclocking

  // Reset behavior: next state is 0; stays 0 while reset is held
  a_rst_next: assert property (RST |-> ##1 (Q == 4'd0));
  a_rst_hold: assert property (RST && $past(RST) |-> (Q == 4'd0 && $stable(Q)));

  // Count up by 1 modulo-16 on every non-reset cycle
  a_inc: assert property (!RST |-> ##1 (Q == $past(Q) + 4'd1));

  // No X/Z on non-reset cycles
  a_known: assert property (!RST |-> !$isunknown(Q));

  // Coverage
  c_reset: cover property ($rose(RST));
  c_wrap:  cover property (!RST && (Q == 4'hF) ##1 (Q == 4'h0));

  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : g_cover_vals
      c_val: cover property (Q == i[3:0]);
    end
  endgenerate
endmodule

bind binary_counter binary_counter_sva u_binary_counter_sva (.CLK(CLK), .RST(RST), .Q(Q));