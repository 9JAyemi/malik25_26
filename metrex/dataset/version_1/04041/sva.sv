// SVA checkers for top_module and its combinational pipeline
// Bind this file to the DUT.
// Focus: correctness, X-propagation checks, and key corner-case coverage.

module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [31:0] data_in,
  input  logic [4:0]  shift_amt,
  input  logic [7:0]  num1,
  input  logic [7:0]  num2,
  input  logic [31:0] shifted_data,
  input  logic [8:0]  sum,
  input  logic [31:0] final_out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Golden expressions
  let sum9      = ({1'b0, num1} + {1'b0, num2});
  let shift32   = (data_in >> shift_amt);
  let sum32     = {{23{1'b0}}, sum};
  let sum9_zext = {{23{1'b0}}, sum9};

  // No-X propagation checks
  assert property( !$isunknown({data_in, shift_amt}) |-> !$isunknown(shifted_data) ) else $error("X in shifted_data");
  assert property( !$isunknown({num1, num2})        |-> !$isunknown(sum)          ) else $error("X in sum");
  assert property( !$isunknown({shifted_data, sum}) |-> !$isunknown(final_out)    ) else $error("X in final_out");

  // Barrel shifter correctness
  assert property( !$isunknown({data_in, shift_amt, shifted_data})
                   |-> shifted_data == shift32 ) else $error("Shifter mismatch");
  // Corner shifter cases
  assert property( !$isunknown({data_in, shift_amt, shifted_data}) && (shift_amt==5'd0)
                   |-> shifted_data == data_in ) else $error("Shifter amt=0 mismatch");
  assert property( !$isunknown({data_in, shift_amt, shifted_data}) && (shift_amt==5'd31)
                   |-> (shifted_data[30:0]==31'b0) && (shifted_data[0]==data_in[31]) ) else $error("Shifter amt=31 mismatch");
  assert property( !$isunknown({data_in, shift_amt, shifted_data}) && (data_in==32'h0)
                   |-> shifted_data==32'h0 ) else $error("Shifter zero-in mismatch");

  // Adder correctness (9-bit carry out)
  assert property( !$isunknown({num1, num2, sum})
                   |-> sum == sum9 ) else $error("Adder mismatch");
  assert property( !$isunknown({num1, num2, sum})
                   |-> sum[8] == sum9[8] ) else $error("Adder carry mismatch");

  // Functional module correctness
  assert property( !$isunknown({shifted_data, sum, final_out})
                   |-> final_out == (shifted_data + sum32) ) else $error("Functional add mismatch");
  assert property( !$isunknown({shifted_data, sum, final_out}) && (sum==9'd0)
                   |-> final_out == shifted_data ) else $error("Functional sum==0 mismatch");

  // End-to-end equivalence (bypasses internal wires)
  assert property( !$isunknown({data_in, shift_amt, num1, num2, final_out})
                   |-> final_out == (shift32 + sum9_zext) ) else $error("Top end-to-end mismatch");

  // Coverage
  // Cover all possible shift amounts
  genvar i;
  generate
    for (i=0; i<32; i++) begin: g_cover_shift
      cover property( !$isunknown(shift_amt) && (shift_amt==i) );
    end
  endgenerate
  // Adder carry/no-carry and extremes
  cover property( !$isunknown({num1,num2,sum}) && (sum[8]==1'b0) );
  cover property( !$isunknown({num1,num2,sum}) && (sum[8]==1'b1) );
  cover property( !$isunknown({num1,num2}) && (num1==8'h00) && (num2==8'h00) );
  cover property( !$isunknown({num1,num2}) && (num1==8'hFF) && (num2==8'hFF) );
  // Final output wrap-around (32-bit overflow)
  cover property( !$isunknown({shifted_data,sum,final_out}) && (sum!=9'd0) && (final_out < shifted_data) );
endmodule

// Bind into top_module to access its internal nets (shifted_data, sum)
bind top_module top_module_sva
(
  .clk        (clk),
  .reset      (reset),
  .data_in    (data_in),
  .shift_amt  (shift_amt),
  .num1       (num1),
  .num2       (num2),
  .shifted_data(shifted_data),
  .sum        (sum),
  .final_out  (final_out)
);