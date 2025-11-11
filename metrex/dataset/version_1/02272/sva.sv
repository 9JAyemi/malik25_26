// SVA checker for adder_subtractor
// Assumes an external clock/reset for sampling; bind as shown below.

module adder_subtractor_sva #(parameter W=4) (
  input logic               clk,
  input logic               rst_n,
  input logic [W-1:0]       A,
  input logic [W-1:0]       B,
  input logic               Cin,
  input logic               Mode,
  input logic [W-1:0]       Sum,
  input logic               Cout
);

  logic [W:0] add_gold, sub_gold, sel_gold;

  always_comb begin
    add_gold = {1'b0, A} + {1'b0, B} + Cin;     // A + B + Cin
    sub_gold = {1'b0, A} + {1'b0, ~B} + 1'b1;   // A - B  (A + ~B + 1)
    sel_gold = Mode ? sub_gold : add_gold;
  end

  default clocking @(posedge clk); endclocking
  default disable iff (!rst_n);

  // No X/Z on outputs when inputs are known
  ap_no_x: assert property (
    !$isunknown({A,B,Cin,Mode}) |-> !$isunknown({Sum,Cout})
  );

  // Functional specification: selected add/sub, with proper carry/borrow in MSB
  ap_func: assert property ( {Cout, Sum} == sel_gold );

  // Coverage: exercise carry/no-carry and borrow/no-borrow cases
  cp_add_no_carry: cover property (Mode==1'b0 && add_gold[W]==1'b0);
  cp_add_carry:    cover property (Mode==1'b0 && add_gold[W]==1'b1);
  cp_sub_no_borrow:cover property (Mode==1'b1 && sub_gold[W]==1'b1);
  cp_sub_borrow:   cover property (Mode==1'b1 && sub_gold[W]==1'b0);

  // Corner cases
  cp_zero_zero:    cover property (Mode==1'b0 && A=={W{1'b0}} && B=={W{1'b0}} && Cin==1'b0);
  cp_max_max_cin:  cover property (Mode==1'b0 && A=={W{1'b1}} && B=={W{1'b1}} && Cin==1'b1);
  cp_sub_equal:    cover property (Mode==1'b1 && A==B);

endmodule

// Bind example (ensure clk and rst_n are visible where DUT is instantiated):
// bind adder_subtractor adder_subtractor_sva #(.W(4))
//   u_adder_subtractor_sva (.clk(clk), .rst_n(rst_n),
//     .A(A), .B(B), .Cin(Cin), .Mode(Mode), .Sum(Sum), .Cout(Cout));