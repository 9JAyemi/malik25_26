// SVA for e0/e1/ch/maj/s0/s1 (concise, high-quality checks)
// Drop into your sim as-is; binds attach to DUT modules.

package sha32_sva_pkg;

  function automatic logic [31:0] rotr32 (logic [31:0] a, int unsigned k);
    return (a >> k) | (a << (32 - k));
  endfunction

  function automatic logic [31:0] shr32 (logic [31:0] a, int unsigned k);
    return a >> k;
  endfunction

  // e0: Σ0 = ROTR2 ^ ROTR13 ^ ROTR22
  module e0_sva (input logic [31:0] x, y);
    logic [31:0] y_ref;
    always_comb y_ref = rotr32(x,2) ^ rotr32(x,13) ^ rotr32(x,22);
    always_comb begin
      if (!$isunknown(x)) assert (!$isunknown(y)) else $error("e0: y X with known x");
      assert (y == y_ref) else $error("e0 mismatch");
      cover (x == 32'h00000000);
      cover (x == 32'hFFFFFFFF);
      cover (x == 32'h00000001);
      cover (x == 32'h80000000);
      cover (x[0] ^ x[31]); // cross-boundary activity
    end
  endmodule

  // e1: Σ1 = ROTR6 ^ ROTR11 ^ ROTR25
  module e1_sva (input logic [31:0] x, y);
    logic [31:0] y_ref;
    always_comb y_ref = rotr32(x,6) ^ rotr32(x,11) ^ rotr32(x,25);
    always_comb begin
      if (!$isunknown(x)) assert (!$isunknown(y)) else $error("e1: y X with known x");
      assert (y == y_ref) else $error("e1 mismatch");
      cover (x == 32'h00000000);
      cover (x == 32'hFFFFFFFF);
      cover (x == 32'h00000001);
      cover (x == 32'h80000000);
      cover (x[5] ^ x[31]); // rotation boundary
    end
  endmodule

  // ch: Ch = (x & y) ^ (~x & z)  (equiv to DUT form)
  module ch_sva (input logic [31:0] x, y, z, o);
    logic [31:0] ref1, ref2;
    always_comb begin
      ref1 = (x & y) ^ (~x & z);
      ref2 = z ^ (x & (y ^ z));
      if (!$isunknown({x,y,z})) assert (!$isunknown(o)) else $error("ch: o X with known inputs");
      assert (o == ref1) else $error("ch mismatch to canonical");
      assert (o == ref2) else $error("ch mismatch to DUT algebra");
      cover (x==32'hFFFFFFFF && y==32'hAAAAAAAA && z==32'h55555555);
      cover (x==32'h00000000 && y==32'hDEADBEEF && z==32'hCAFEBABE);
      cover (x==32'hFFFFFFFF && y==32'hDEADBEEF && z==32'hCAFEBABE);
    end
  endmodule

  // maj: Maj = (x & y) | (x & z) | (y & z)
  module maj_sva (input logic [31:0] x, y, z, o);
    logic [31:0] ref1, ref2;
    always_comb begin
      ref1 = (x & y) | (x & z) | (y & z);
      ref2 = (x & y) | (z & (x | y)); // DUT algebra
      if (!$isunknown({x,y,z})) assert (!$isunknown(o)) else $error("maj: o X with known inputs");
      assert (o == ref1) else $error("maj mismatch to canonical");
      assert (o == ref2) else $error("maj mismatch to DUT algebra");
      cover (x==32'h00000000 && y==32'hFFFFFFFF && z==32'h00000000);
      cover (x==32'hFFFFFFFF && y==32'h00000000 && z==32'hFFFFFFFF);
      cover (x==32'hAAAAAAAA && y==32'h55555555 && z==32'hFFFFFFFF);
    end
  endmodule

  // s0: σ0 = ROTR7 ^ ROTR18 ^ SHR3
  module s0_sva (input logic [31:0] x, y);
    logic [31:0] y_ref;
    always_comb y_ref = rotr32(x,7) ^ rotr32(x,18) ^ shr32(x,3);
    always_comb begin
      if (!$isunknown(x)) assert (!$isunknown(y)) else $error("s0: y X with known x");
      assert (y == y_ref) else $error("s0 mismatch");
      // spot covers to hit both top-slice and lower-slice logic
      cover (x == 32'h00000001);
      cover (x == 32'h00000008); // affects SHR3 LSB intake
      cover (x == 32'h80000000); // rotation MSB->LSB
      cover (x[6] ^ x[17]);      // targets y[31:29] split path
    end
  endmodule

  // s1: σ1 = ROTR17 ^ ROTR19 ^ SHR10
  module s1_sva (input logic [31:0] x, y);
    logic [31:0] y_ref;
    always_comb y_ref = rotr32(x,17) ^ rotr32(x,19) ^ shr32(x,10);
    always_comb begin
      if (!$isunknown(x)) assert (!$isunknown(y)) else $error("s1: y X with known x");
      assert (y == y_ref) else $error("s1 mismatch");
      cover (x == 32'h00000400); // hits SHR10 boundary
      cover (x == 32'h00000001);
      cover (x == 32'h80000000);
      cover (x[16] ^ x[18]);     // targets y[31:22] split path
    end
  endmodule

endpackage

// Bind the SVA to the DUTs
import sha32_sva_pkg::*;

bind e0  sha32_sva_pkg::e0_sva  e0_chk (.x(x), .y(y));
bind e1  sha32_sva_pkg::e1_sva  e1_chk (.x(x), .y(y));
bind ch  sha32_sva_pkg::ch_sva  ch_chk (.x(x), .y(y), .z(z), .o(o));
bind maj sha32_sva_pkg::maj_sva maj_chk(.x(x), .y(y), .z(z), .o(o));
bind s0  sha32_sva_pkg::s0_sva  s0_chk (.x(x), .y(y));
bind s1  sha32_sva_pkg::s1_sva  s1_chk (.x(x), .y(y));