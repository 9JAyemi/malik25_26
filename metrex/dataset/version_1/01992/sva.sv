// SVA for abs_bcd_converter/top_module
// Focus: correctness of BCD conversion, absolute value, and packed abs_bcd_val
// Bind into top_module

module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  binary,
  input logic [3:0]  bcd_high,
  input logic [3:0]  bcd_low,
  input logic [3:0]  abs_val,
  input logic [11:0] abs_bcd_val
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Helpers
  function automatic logic [3:0] tens4 (input logic [3:0] u);
    tens4 = (u > 4'd9) ? 4'd1 : 4'd0;
  endfunction

  function automatic logic [3:0] ones4 (input logic [3:0] u);
    ones4 = (u > 4'd9) ? (u - 4'd10) : u;
  endfunction

  function automatic logic [7:0] bcd_to_u8 (input logic [3:0] hi, input logic [3:0] lo);
    bcd_to_u8 = (hi * 8'd10) + lo;
  endfunction

  // Sanity (no X/Z)
  assert property ( !$isunknown({binary,bcd_high,bcd_low,abs_val,abs_bcd_val}) )
    else $error("X/Z detected on IOs");

  // bcd_converter: digits valid and correct numeric value
  assert property ( (bcd_high <= 4'd9) && (bcd_low <= 4'd9) )
    else $error("BCD digits out of range");

  assert property ( bcd_to_u8(bcd_high,bcd_low) == {4'b0000,binary} )
    else $error("BCD does not match binary value");

  // Strengthen with explicit ranges
  assert property ( (binary <= 4'd9) |-> (bcd_high==4'd0 && bcd_low==binary) )
    else $error("BCD mapping wrong for 0..9");

  assert property ( (binary >= 4'd10) |-> (bcd_high==4'd1 && bcd_low==(binary-4'd10)) )
    else $error("BCD mapping wrong for 10..15");

  // absolute_value: two's complement magnitude, and range (0..8)
  assert property ( abs_val == (binary[3] ? (~binary + 4'd1) : binary) )
    else $error("abs_val incorrect");

  assert property ( abs_val <= 4'd8 )
    else $error("abs_val out of range");

  // abs_bcd_val: {sign,tens,ones} for absolute magnitude; sign reflects original sign
  assert property ( abs_bcd_val[11:8] == (binary[3] ? 4'b0001 : 4'b0000) )
    else $error("abs_bcd_val sign nibble incorrect");

  assert property ( (abs_bcd_val[7:4] <= 4'd9) && (abs_bcd_val[3:0] <= 4'd9) )
    else $error("abs_bcd_val digits out of range");

  assert property ( {abs_bcd_val[7:4],abs_bcd_val[3:0]} == {tens4(abs_val),ones4(abs_val)} )
    else $error("abs_bcd_val digits do not encode abs_val");

  // Functional coverage
  covergroup cg_vals @(posedge clk);
    coverpoint binary { bins all[] = {[0:15]}; }
  endgroup
  cg_vals cg_vals_i = new();

  cover property ( binary[3]==1 );         // negative inputs seen
  cover property ( binary==4'b1000 );      // corner: -8
  cover property ( binary==4'd9 );         // boundary: 9
  cover property ( !binary[3] );           // non-negative inputs seen

endmodule

bind top_module top_module_sva top_module_sva_b (.*);