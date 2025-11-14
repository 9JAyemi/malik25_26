// SVA for adder: bindable, concise, full functional checks + key coverage
module adder_sva (
  input  logic [7:0] A,
  input  logic [7:0] B,
  input  logic       Cin,
  input  logic [7:0] Sum,
  input  logic       Cout
);
  // Fire assertions/coverage on any combinational activity, sample outputs after ##0 to avoid delta races
  event comb_ev;
  always @(A or B or Cin or Sum or Cout) -> comb_ev;

  // Core arithmetic correctness: both Sum and Cout in one check
  ap_core: assert property (@(comb_ev) 1'b1 |-> ##0 ({Cout,Sum} == ({1'b0,A}+{1'b0,B}+Cin)));

  // Outputs must be known if inputs are known
  ap_known: assert property (@(comb_ev) !$isunknown({A,B,Cin}) |-> ##0 !$isunknown({Sum,Cout}));

  // Boundary-specific checks
  ap_255: assert property (@(comb_ev)
                           (({1'b0,A}+{1'b0,B}+Cin)==9'd255) |-> ##0 (Cout==1'b0 && Sum==8'hFF));
  ap_256: assert property (@(comb_ev)
                           (({1'b0,A}+{1'b0,B}+Cin)==9'd256) |-> ##0 (Cout==1'b1 && Sum==8'h00));
  ap_511: assert property (@(comb_ev)
                           (({1'b0,A}+{1'b0,B}+Cin)==9'd511) |-> ##0 (Cout==1'b1 && Sum==8'hFF));

  // Functional coverage (key corners and carry behavior)
  cp_cout0: cover property (@(comb_ev) ##0 (! $isunknown({A,B,Cin}) && Cout==1'b0));
  cp_cout1: cover property (@(comb_ev) ##0 (! $isunknown({A,B,Cin}) && Cout==1'b1));
  cp_cin0:  cover property (@(comb_ev) ##0 (Cin==1'b0));
  cp_cin1:  cover property (@(comb_ev) ##0 (Cin==1'b1));
  cp_0:     cover property (@(comb_ev) ##0 (({1'b0,A}+{1'b0,B}+Cin)==9'd0));
  cp_255:   cover property (@(comb_ev) ##0 (({1'b0,A}+{1'b0,B}+Cin)==9'd255));
  cp_256:   cover property (@(comb_ev) ##0 (({1'b0,A}+{1'b0,B}+Cin)==9'd256));
  cp_511:   cover property (@(comb_ev) ##0 (({1'b0,A}+{1'b0,B}+Cin)==9'd511));
endmodule

bind adder adder_sva (.A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout));