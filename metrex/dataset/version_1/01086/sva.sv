// SVA for ripple_bcd_adder and binary_to_bcd_converter
// Provide a free-running clk and active-low reset_n from the TB.
// Bind examples are at the bottom.

// Assertions for top-level ripple_bcd_adder
module ripple_bcd_adder_sva (
  input logic              clk,
  input logic              reset_n,
  input logic [3:0]        A,
  input logic [3:0]        B,
  input logic              select,
  input logic [3:0]        binary_sum,
  input logic [3:0]        BCD0,
  input logic [3:0]        BCD1,
  input logic [7:0]        bcd_sum
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n)

  // Binary adder correctness (4-bit wrap)
  assert property (
    !$isunknown({A,B}) |-> ($unsigned(binary_sum) == (($unsigned(A)+$unsigned(B)) & 4'hF))
  ) else $error("binary_sum != (A+B)&4'hF");

  // Select gating
  assert property ( !select |-> (BCD0==4'h0 && BCD1==4'h0) )
    else $error("Outputs not zeroed when select==0");

  // Correct routing when selected
  assert property ( select |-> {BCD1,BCD0} == bcd_sum )
    else $error("BCD outputs do not match bcd_sum slices when select==1");

  // Known-ness: when inputs known, outputs known
  assert property ( !$isunknown({A,B,select}) |-> !$isunknown({binary_sum,BCD0,BCD1}) )
    else $error("Unknown on outputs with known inputs");

  // Coverage
  cover property ( !select );
  cover property ( select );
  cover property ( A==4'h0 && B==4'h0 );
  cover property ( A==4'hF && B==4'hF );
  cover property ( select && {BCD1,BCD0} == bcd_sum );
  cover property ( !select && BCD0==4'h0 && BCD1==4'h0 );
endmodule


// Assertions for binary_to_bcd_converter
module binary_to_bcd_converter_sva (
  input logic        clk,
  input logic        reset_n,
  input logic [3:0]  binary_in,
  input logic [7:0]  bcd_out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n)

  // Known-ness
  assert property ( !$isunknown(binary_in) |-> !$isunknown(bcd_out) )
    else $error("Unknown bcd_out with known binary_in");

  // Exact LUT mapping (matches DUT case table)
  assert property (
    !$isunknown(binary_in) |->
      ((binary_in==4'h0 && bcd_out==8'b00000001) ||
       (binary_in==4'h1 && bcd_out==8'b00000010) ||
       (binary_in==4'h2 && bcd_out==8'b00000100) ||
       (binary_in==4'h3 && bcd_out==8'b00000110) ||
       (binary_in==4'h4 && bcd_out==8'b00001000) ||
       (binary_in==4'h5 && bcd_out==8'b00001010) ||
       (binary_in==4'h6 && bcd_out==8'b00001100) ||
       (binary_in==4'h7 && bcd_out==8'b00001110) ||
       (binary_in==4'h8 && bcd_out==8'b00010000) ||
       (binary_in==4'h9 && bcd_out==8'b00010001) ||
       (binary_in==4'hA && bcd_out==8'b00010010) ||
       (binary_in==4'hB && bcd_out==8'b00010011) ||
       (binary_in==4'hC && bcd_out==8'b00010100) ||
       (binary_in==4'hD && bcd_out==8'b00010101) ||
       (binary_in==4'hE && bcd_out==8'b00010110) ||
       (binary_in==4'hF && bcd_out==8'b00010111))
  ) else $error("binary_to_bcd_converter mapping mismatch");

  // Cover all input codes 0..15
  genvar i;
  generate
    for (i=0;i<16;i++) begin: cov_vals
      cover property ( binary_in == i[3:0] );
    end
  endgenerate
endmodule


// Example binds (edit clk/reset_n names to match your TB)
// bind ripple_bcd_adder        ripple_bcd_adder_sva        u_ripple_bcd_adder_sva        (.clk(clk), .reset_n(reset_n), .A(A), .B(B), .select(select), .binary_sum(binary_sum), .BCD0(BCD0), .BCD1(BCD1), .bcd_sum(bcd_sum));
// bind binary_to_bcd_converter binary_to_bcd_converter_sva u_binary_to_bcd_converter_sva (.clk(clk), .reset_n(reset_n), .binary_in(binary_in), .bcd_out(bcd_out));