// SVA for binary_to_excess3, binary_to_bcd, and top_module
// Clockless, concise, and functional (golden-model) checks with targeted coverage.

`ifndef SVA_BTBC_EX3_TOP
`define SVA_BTBC_EX3_TOP

// ------------------------
// SVA for binary_to_excess3
// ------------------------
module sva_binary_to_excess3 (
  input logic [3:0] binary_in,
  input logic [3:0] excess3_out
);
  // Golden model: Excess-3 = (binary + 3) mod 16
  let ex3_g = (binary_in + 4'd3) & 4'hF;

  // Sanity: no X/Z on I/O
  assert property (!$isunknown(binary_in));
  assert property (!$isunknown(excess3_out));

  // Functional equivalence
  assert property (excess3_out == ex3_g)
    else $error("binary_to_excess3: excess3_out != (binary_in + 3)%%16. bin=%0d got=%0d exp=%0d",
                binary_in, excess3_out, ex3_g);

  // Minimal coverage (boundary cases)
  cover property (binary_in == 4'd0  && excess3_out == 4'd3);
  cover property (binary_in == 4'd9  && excess3_out == 4'd12);
  cover property (binary_in == 4'd10 && excess3_out == 4'd13);
  cover property (binary_in == 4'd15 && excess3_out == 4'd2);
endmodule

bind binary_to_excess3 sva_binary_to_excess3
  i_sva_binary_to_excess3(.binary_in(binary_in), .excess3_out(excess3_out));


// ------------------------
// SVA for binary_to_bcd
// ------------------------
module sva_binary_to_bcd (
  input logic [3:0] binary_in,
  input logic [7:0] bcd_out,
  input logic       overflow
);
  // Golden model: 4-bit binary to BCD {tens, ones} and overflow for >9
  let tens_g = (binary_in > 4'd9) ? 4'd1 : 4'd0;
  let ones_g = (binary_in > 4'd9) ? (binary_in - 4'd10) : binary_in;

  // Sanity: no X/Z on I/O
  assert property (!$isunknown(binary_in));
  assert property (!$isunknown(bcd_out));
  assert property (!$isunknown(overflow));

  // Functional mapping
  assert property (bcd_out[7:4] == tens_g && bcd_out[3:0] == ones_g)
    else $error("binary_to_bcd: BCD mismatch. bin=%0d got={%0d,%0d} exp={%0d,%0d}",
                binary_in, bcd_out[7:4], bcd_out[3:0], tens_g, ones_g);

  // Overflow definition
  assert property (overflow == (binary_in > 4'd9))
    else $error("binary_to_bcd: overflow mismatch. bin=%0d ovf=%0b exp=%0b",
                binary_in, overflow, (binary_in > 4'd9));

  // Coverage: below/at/above threshold
  cover property (binary_in == 4'd0  && bcd_out == 8'h00 && !overflow);
  cover property (binary_in == 4'd9  && bcd_out == {4'd0,4'd9} && !overflow);
  cover property (binary_in == 4'd10 && bcd_out == {4'd1,4'd0} && overflow);
  cover property (binary_in == 4'd15 && bcd_out == {4'd1,4'd5} && overflow);
endmodule

bind binary_to_bcd sva_binary_to_bcd
  i_sva_binary_to_bcd(.binary_in(binary_in), .bcd_out(bcd_out), .overflow(overflow));


// ------------------------
// SVA for top_module
// ------------------------
module sva_top_module (
  input  logic [3:0] B,
  input  logic [7:0] bcd_out,
  input  logic       overflow,
  input  logic [3:0] E,
  input  logic [3:0] sum
);
  // Golden excess-3 of B
  let ex3B = (B + 4'd3) & 4'hF;
  let tens_ex3 = (ex3B > 4'd9) ? 4'd1 : 4'd0;
  let ones_ex3 = (ex3B > 4'd9) ? (ex3B - 4'd10) : ex3B;

  // Sanity: no X/Z on top I/O
  assert property (!$isunknown(B));
  assert property (!$isunknown(E));
  assert property (!$isunknown(sum));
  assert property (!$isunknown(bcd_out));
  assert property (!$isunknown(overflow));

  // E driven by bin2ex3
  assert property (E == ex3B)
    else $error("top: E != (B+3)%%16. B=%0d E=%0d exp=%0d", B, E, ex3B);

  // sum = B + E (4-bit wrap)
  assert property (sum == ((B + E) & 4'hF))
    else $error("top: sum != (B+E)%%16. B=%0d E=%0d sum=%0d exp=%0d", B, E, sum, ((B+E)&4'hF));

  // BCD corresponds to Excess-3(B)
  assert property (bcd_out[7:4] == tens_ex3 && bcd_out[3:0] == ones_ex3)
    else $error("top: bcd_out mismatch vs Ex3(B). B=%0d ex3=%0d got={%0d,%0d} exp={%0d,%0d}",
                B, ex3B, bcd_out[7:4], bcd_out[3:0], tens_ex3, ones_ex3);

  // Overflow corresponds to Ex3(B) > 9
  assert property (overflow == (ex3B > 4'd9))
    else $error("top: overflow mismatch vs Ex3(B). B=%0d ex3=%0d ovf=%0b exp=%0b",
                B, ex3B, overflow, (ex3B > 4'd9));

  // Coverage: both BCD regions reachable via Ex3(B)
  cover property (ex3B <= 4'd9  && bcd_out[7:4] == 4'd0);
  cover property (ex3B >= 4'd10 && bcd_out[7:4] == 4'd1);
endmodule

bind top_module sva_top_module
  i_sva_top_module(.B(B), .bcd_out(bcd_out), .overflow(overflow), .E(E), .sum(sum));

`endif