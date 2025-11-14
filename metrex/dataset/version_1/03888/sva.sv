// SVA for adder_subtractor
module adder_subtractor_sva
(
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       Cin,
  input  logic       Sel,
  input  logic [3:0] S,
  input  logic       Cout,
  // internal DUT nets (bound by name)
  input  logic [3:0] temp_sum,
  input  logic       temp_carry
);
  default clocking cb @(posedge $global_clock); endclocking

  // Functional correctness
  ap_add:       assert property (!Sel |-> {Cout,S} == A + B + Cin);
  ap_sub_s:     assert property ( Sel |-> S == (A - B));
  ap_sub_cout:  assert property ( Sel |-> Cout == (A[3]^B[3]^Cin));

  // Structural mapping to internals
  ap_s_from_tmp: assert property (S == temp_sum);
  ap_cout_mux:   assert property (Cout == (Sel ? (A[3]^B[3]^Cin) : temp_carry));

  // X-propagation and combinational stability
  ap_no_x:     assert property (!$isunknown({A,B,Cin,Sel})) |-> !$isunknown({S,Cout,temp_sum,temp_carry});
  ap_stable:   assert property ($stable({A,B,Cin,Sel}) |=> $stable({S,Cout,temp_sum,temp_carry}));

  // Coverage
  cp_add_cin0_no_carry: cover property (!Sel && (Cin==0) && ({Cout,S} == A + B + 1'b0) && (Cout==0));
  cp_add_cin1_carry:    cover property (!Sel && (Cin==1) && ({Cout,S} == A + B + 1'b1) && (Cout==1));
  cp_add_overflow:      cover property (!Sel && (Cout==1));
  cp_sub_equal:         cover property ( Sel && (A==B) && (S==4'h0));
  cp_sub_underflow:     cover property ( Sel && (A<B));
  cp_sel_toggle:        cover property ( Sel ##1 !Sel ##1 Sel );
endmodule

bind adder_subtractor adder_subtractor_sva i_adder_subtractor_sva (.*);