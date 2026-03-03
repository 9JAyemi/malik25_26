// SVA checkers and binds for ripple_carry_adder and full_adder.
// Assertions sample on posedge clk. Provide a clock named 'clk' in the bind scope.

module rca_sva (
  input logic        clk,
  input logic [3:0]  a, b, sum,
  input logic        carry_out,
  input logic [2:0]  c   // internal carries: c[0]=fa0.cout, c[1]=fa1.cout, c[2]=fa2.cout
);
  default clocking cb @(posedge clk); endclocking

  // No X/Z on inputs/outputs/internals
  assert property (!$isunknown({a,b,sum,carry_out,c}));

  // Top-level arithmetic equivalence (extend before add to keep carry)
  assert property ( {carry_out,sum} == ({1'b0,a} + {1'b0,b}) );

  // Bit 0 (cin=0)
  assert property ( sum[0] == (a[0] ^ b[0]) );
  assert property ( c[0]   == (a[0] & b[0]) );

  // Bits 1..2
  genvar i;
  generate
    for (i=1; i<3; i++) begin : gen_mid_bits
      assert property ( sum[i] == (a[i] ^ b[i] ^ c[i-1]) );
      assert property ( c[i]   == ((a[i]&b[i]) | (a[i]&c[i-1]) | (b[i]&c[i-1])) );
    end
  endgenerate

  // Bit 3 and final carry
  assert property ( sum[3]     == (a[3] ^ b[3] ^ c[2]) );
  assert property ( carry_out  == ((a[3]&b[3]) | (a[3]&c[2]) | (b[3]&c[2])) );

  // Concise functional coverage
  cover property ( carry_out );                              // overflow seen
  cover property ( !(|{c,carry_out}) );                      // no carries anywhere
  cover property ( c[0] && c[1] && c[2] && carry_out );      // heavy carry activity through all stages
  cover property ( (sum == 4'h0) && (carry_out == 1'b0) );   // 0 + 0 -> 0
  cover property ( (sum == 4'hF) && (carry_out == 1'b0) );   // max 4-bit sum without overflow
  cover property ( (sum == 4'h0) && (carry_out == 1'b1) );   // 8+8 (or similar) -> wrap with carry
endmodule


module fa_sva (
  input logic clk,
  input logic a, b, cin,
  input logic cout, sum
);
  default clocking cb @(posedge clk); endclocking

  // No X/Z
  assert property (!$isunknown({a,b,cin,sum,cout}));

  // Arithmetic and logic equivalence (extend before add)
  assert property ( {cout,sum} == ({1'b0,a} + {1'b0,b} + {1'b0,cin}) );
  assert property ( sum  == (a ^ b ^ cin) );
  assert property ( cout == ((a & b) | (a & cin) | (b & cin)) );

  // Full input-space coverage (8 combos)
  cover property ( {a,b,cin} == 3'b000 );
  cover property ( {a,b,cin} == 3'b001 );
  cover property ( {a,b,cin} == 3'b010 );
  cover property ( {a,b,cin} == 3'b011 );
  cover property ( {a,b,cin} == 3'b100 );
  cover property ( {a,b,cin} == 3'b101 );
  cover property ( {a,b,cin} == 3'b110 );
  cover property ( {a,b,cin} == 3'b111 );
endmodule


// Bind checkers to DUTs. Requires a clock 'clk' visible in the bound scope.
bind ripple_carry_adder rca_sva rca_chk (
  .clk       (clk),
  .a         (a),
  .b         (b),
  .sum       (sum),
  .carry_out (carry_out),
  .c         (carry[2:0])
);

bind full_adder fa_sva fa_chk (
  .clk (clk),
  .a   (a),
  .b   (b),
  .cin (cin),
  .cout(cout),
  .sum (sum)
);