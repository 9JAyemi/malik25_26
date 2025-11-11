// SVA checker for adder_subtractor (concise, high-quality)
module adder_subtractor_sva (
  input logic        clk,
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic        SUB,
  input logic [3:0]  SUM,
  input logic        C_OUT
);

  function automatic logic [4:0] add5 (input logic [3:0] a, b);
    add5 = {1'b0,a} + {1'b0,b};
  endfunction

  function automatic logic [4:0] sub5 (input logic [3:0] a, b);
    sub5 = {1'b0,a} - {1'b0,b};
  endfunction

  default clocking cb @(posedge clk); endclocking

  // Correctness (inputs known -> outputs are exactly the expected 5-bit result)
  ap_comb: assert property ( !$isunknown({A,B,SUB})
                             |-> ##0 {C_OUT,SUM} == (SUB ? sub5(A,B) : add5(A,B)) );

  // Mode-specific checks
  ap_add:  assert property ( (!$isunknown({A,B}) && SUB==1'b0)
                             |-> ##0 {C_OUT,SUM} == add5(A,B) );
  ap_sub:  assert property ( (!$isunknown({A,B}) && SUB==1'b1)
                             |-> ##0 {C_OUT,SUM} == sub5(A,B) );

  // Outputs never X/Z when inputs known
  ap_no_x: assert property ( !$isunknown({A,B,SUB}) |-> ##0 !$isunknown({SUM,C_OUT}) );

  // Flag semantics
  ap_cout_add: assert property ( (!$isunknown({A,B}) && SUB==1'b0)
                                 |-> ##0 C_OUT == (A + B > 4'hF) );
  ap_cout_sub: assert property ( (!$isunknown({A,B}) && SUB==1'b1)
                                 |-> ##0 C_OUT == (A < B) );

  // Addition commutativity (sanity)
  ap_comm_add: assert property ( (!$isunknown({A,B}) && SUB==1'b0)
                                 |-> ##0 {C_OUT,SUM} == add5(B,A) );

  // Targeted functional coverage
  cp_add_mode:   cover property (SUB==1'b0);
  cp_sub_mode:   cover property (SUB==1'b1);
  cp_add_carry:  cover property (SUB==1'b0 && (A + B > 4'hF));
  cp_add_edge:   cover property (SUB==1'b0 && (A + B == 4'hF));
  cp_sub_borrow: cover property (SUB==1'b1 && (A < B));
  cp_sub_equal:  cover property (SUB==1'b1 && (A == B));
  cp_minmin:     cover property (SUB==1'b0 && A==4'h0 && B==4'h0);
  cp_maxmax:     cover property (SUB==1'b0 && A==4'hF && B==4'hF);
  cp_minmax_sub: cover property (SUB==1'b1 && A==4'h0 && B==4'hF);
  cp_maxmin_sub: cover property (SUB==1'b1 && A==4'hF && B==4'h0);
  cp_sub_rose:   cover property ($rose(SUB));
  cp_sub_fell:   cover property ($fell(SUB));

endmodule

// Bind into DUT. Replace tb_clk with your testbench sampling clock.
bind adder_subtractor adder_subtractor_sva u_adder_subtractor_sva (
  .clk(tb_clk),
  .A(A),
  .B(B),
  .SUB(SUB),
  .SUM(SUM),
  .C_OUT(C_OUT)
);