// SVA for add4: bindable, concise, and complete

module add4_sva (input logic [3:0] A, B,
                 input logic [4:0] C);

  // Sample on any combinational change
  default clocking cb @(*); endclocking

  // Correctness (guard against X/Z on inputs)
  property p_sum_correct;
    !$isunknown({A,B}) |-> (C == ({1'b0,A} + {1'b0,B}));
  endproperty
  assert property (p_sum_correct);

  // Bitwise checks (redundant but catches wiring mistakes)
  assert property (!$isunknown({A,B}) |-> (C[3:0] == (A + B)));
  assert property (!$isunknown({A,B}) |-> (C[4]   == ({1'b0,A} + {1'b0,B})[4]));

  // No X/Z on output when inputs are known
  assert property (!$isunknown({A,B}) |-> !$isunknown(C));

  // Key functional coverage
  cover property (!$isunknown({A,B})) && (({1'b0,A}+{1'b0,B}) < 16);   // no carry
  cover property (!$isunknown({A,B})) && (({1'b0,A}+{1'b0,B}) >= 16);  // carry
  cover property (!$isunknown({A,B})) && (A==4'h0 && B==4'h0);
  cover property (!$isunknown({A,B})) && (A==4'hF && B==4'hF);
  cover property (!$isunknown({A,B})) && (A==4'hF && B==4'h1);
  cover property (!$isunknown({A,B})) && (A==4'h0 && B==4'hF);

  // Full value coverage: all 256 input combinations
  covergroup cg_ab @(A or B);
    option.per_instance = 1;
    A_bins: coverpoint A iff (!$isunknown({A,B})) { bins all[] = {[0:15]}; }
    B_bins: coverpoint B iff (!$isunknown({A,B})) { bins all[] = {[0:15]}; }
    AB_cross: cross A_bins, B_bins;
  endgroup
  cg_ab cg = new();

endmodule

bind add4 add4_sva sva_add4 (.*);