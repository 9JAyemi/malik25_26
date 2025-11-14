// SVA checker for ripple_adder
module ripple_adder_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [3:0]  A,
  input  logic [3:0]  B,
  input  logic        Cin,
  input  logic [3:0]  Sum,
  input  logic        Cout
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  function automatic logic [4:0] ref_add(logic [3:0] a, b, logic cin);
    ref_add = a + b + cin;
  endfunction

  // Cleanliness
  a_no_x_in_out: assert property ( !$isunknown({A,B,Cin}) |-> !$isunknown({Sum,Cout}) );
  a_stable_when_inputs_stable: assert property ( $stable({A,B,Cin}) |-> $stable({Sum,Cout}) );

  // Functional correctness
  a_add_correct: assert property ( !$isunknown({A,B,Cin}) |-> {Cout,Sum} == ref_add(A,B,Cin) );
  a_commutative: assert property ( !$isunknown({A,B,Cin}) |-> {Cout,Sum} == ref_add(B,A,Cin) );

  // Useful corner-case coverage
  c_no_carry:          cover property ( ref_add(A,B,Cin)[4] == 1'b0 );
  c_with_carry:        cover property ( ref_add(A,B,Cin)[4] == 1'b1 );
  c_full_propagate:    cover property ( (A^B)==4'hF && Cin && {Cout,Sum}==5'h10 );
  c_zero_inputs:       cover property ( A==4'h0 && B==4'h0 && !Cin && {Cout,Sum}==5'h00 );
  c_max_plus_max:      cover property ( A==4'hF && B==4'hF && !Cin && {Cout,Sum}==5'd30 );
  c_random_mix:        cover property ( A==4'hA && B==4'h5 && Cin && {Cout,Sum}==5'd16 );

  // Optional full input-space functional coverage (concise)
  covergroup cg_inputs @(cb);
    cp: coverpoint {A,B,Cin} { bins all[] = {[0:511]}; }
  endgroup
  cg_inputs cg = new();

endmodule

// Bind into DUT (provide clk/rst_n from TB)
// bind ripple_adder ripple_adder_sva u_ripple_adder_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));