// SVA checker for four_bit_adder
module four_bit_adder_sva (
  input logic [3:0] a, b, sum,
  input logic       cin, cout
);
  default clocking cb @(*); endclocking

  // 5-bit golden sum (captures carry-out)
  wire [4:0] full_sum = {1'b0, a} + {1'b0, b} + cin;

  // Sanity: no X/Z on interface
  assert property (!$isunknown({a,b,cin,sum,cout}));

  // Functional equivalence: {cout,sum} must equal a+b+cin
  assert property ({cout, sum} == full_sum);

  // Minimal functional coverage
  cover property (cout == 0);
  cover property (cout == 1);
  cover property (sum == 4'h0);
  cover property (sum == 4'hF);
  cover property (a==4'h0 && b==4'h0 && cin==1'b0);
  cover property (a==4'hF && b==4'hF && cin==1'b1);
endmodule

// Bind into DUT
bind four_bit_adder four_bit_adder_sva sva_i(.*);