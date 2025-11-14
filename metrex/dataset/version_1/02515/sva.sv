// SVA for pipelined_multiplier
// Bind into DUT to access internals

module pipelined_multiplier_sva (input logic clk, input logic [15:0] A, B, input logic [31:0] P);
  default clocking cb @(posedge clk); endclocking

  bit p1, p2, p3;
  always @(posedge clk) begin
    p1 <= 1'b1;
    p2 <= p1;
    p3 <= p2;
  end

  // Input sampling into stage-0 regs
  ap_sample_regs: assert property (p1 |-> (a_reg == $past(A) && b_reg == $past(B)));

  // Combinational partial products
  ap_pp1_comb: assert property (pp1 == (a_reg[0] ? b_reg : 16'h0));
  ap_pp2_comb: assert property (pp2 == (a_reg[1] ? {b_reg[14:0],1'b0} : 16'h0));
  ap_pp3_comb: assert property (pp3 == (a_reg[2] ? {b_reg[13:0],2'b00} : 16'h0));
  ap_pp4_comb: assert property (pp4 == (a_reg[3] ? {b_reg[12:0],3'b000} : 16'h0));

  // Pipe registers capture pp wires
  ap_pp_pipe: assert property (p1 |-> (pp1_reg == $past(pp1)
                                    && pp2_reg == $past(pp2)
                                    && pp3_reg == $past(pp3)
                                    && pp4_reg == $past(pp4)));

  // Final sum register behavior
  ap_P_hi_zero:  assert property (P[31:16] == 16'h0);
  ap_P_from_pp:  assert property (p1 |-> P[15:0] == $past(pp1_reg + pp2_reg + pp3_reg + pp4_reg));

  // End-to-end functional check (3-cycle latency, low-16b of B * low nibble of A)
  ap_e2e: assert property (p3 |-> (P[31:16] == 16'h0
                                && P[15:0] == ($past(B,3) * $past(A,3)[3:0])));

  // Corner-case implications (optional but tight)
  ap_zero_when_zeroA: assert property (p3 && ($past(A,3)[3:0] == 4'h0) |-> P == 32'h0);
  ap_zero_when_zeroB: assert property (p3 && ($past(B,3) == 16'h0)     |-> P == 32'h0);

  // Lightweight coverage
  cp_pp1_used: cover property (p1 && (pp1_reg != 16'h0));
  cp_pp2_used: cover property (p1 && (pp2_reg != 16'h0));
  cp_pp3_used: cover property (p1 && (pp3_reg != 16'h0));
  cp_pp4_used: cover property (p1 && (pp4_reg != 16'h0));
  cp_full_load: cover property (p3 && ($past(A,3)[3:0] == 4'hF) && ($past(B,3) == 16'hFFFF));
endmodule

bind pipelined_multiplier pipelined_multiplier_sva sva_i (.clk(clk), .A(A), .B(B), .P(P));