// SVA for full_adder_2bit
// Binds self-checking functional assertions and concise coverage.

module full_adder_2bit_sva (
  input  logic [1:0] A,
  input  logic [1:0] B,
  input  logic       Cin,
  input  logic [1:0] Sum,
  input  logic       Cout
);

  function automatic logic [2:0] exp_sum(input logic [1:0] a, b, input logic cin);
    return {1'b0,a} + {1'b0,b} + cin;
  endfunction

  // Functional correctness (combinational, 0-delay settle)
  ap_func: assert property (@(A or B or Cin) ##0 {Cout,Sum} == exp_sum(A,B,Cin))
    else $error("full_adder_2bit mismatch: A=%b B=%b Cin=%b -> got {Cout,Sum}=%b%b exp=%b",
                A,B,Cin,Cout,Sum,exp_sum(A,B,Cin));

  // No X/Z on outputs when inputs are known
  ap_no_x_when_inputs_known: assert property (@(A or B or Cin)
      !$isunknown({A,B,Cin}) |-> ##0 !$isunknown({Cout,Sum}))
    else $error("full_adder_2bit produced X/Z outputs for known inputs: A=%b B=%b Cin=%b -> {Cout,Sum}=%b%b",
                A,B,Cin,Cout,Sum);

  // Basic coverage: exercise carry/no-carry, range extremes, and all Sum patterns
  cp_carry0: cover property (@(A or B or Cin) ##0 exp_sum(A,B,Cin)[2] == 1'b0);
  cp_carry1: cover property (@(A or B or Cin) ##0 exp_sum(A,B,Cin)[2] == 1'b1);

  cp_min:    cover property (@(A or B or Cin) ##0 exp_sum(A,B,Cin) == 3'd0);
  cp_max:    cover property (@(A or B or Cin) ##0 exp_sum(A,B,Cin) == 3'd7);

  cp_sum00:  cover property (@(A or B or Cin) ##0 Sum == 2'b00);
  cp_sum01:  cover property (@(A or B or Cin) ##0 Sum == 2'b01);
  cp_sum10:  cover property (@(A or B or Cin) ##0 Sum == 2'b10);
  cp_sum11:  cover property (@(A or B or Cin) ##0 Sum == 2'b11);

  // Full truth-table input coverage (all 32 input combinations)
  covergroup cg_inputs @(A or B or Cin);
    option.per_instance = 1;
    coverpoint {A,B,Cin} { bins all[] = {[0:31]}; }
    coverpoint {Cout,Sum} { bins all[] = {[0:7]}; }
  endgroup
  cg_inputs cg_i = new;

endmodule

bind full_adder_2bit full_adder_2bit_sva sva_i (
  .A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout)
);