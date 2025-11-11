// SVA for twos_complement
// Focused, clockless, and bindable

`ifndef TWOS_COMPLEMENT_SVA_SV
`define TWOS_COMPLEMENT_SVA_SV

module twos_complement_sva (
  input logic [3:0] binary,
  input logic [3:0] twos_comp
);

  // Expected function (mod 16)
  let exp = ((~binary) + 4'd1)[3:0];

  // Functional correctness
  assert property (@(binary or twos_comp) twos_comp === exp)
    else $error("twos_complement mismatch: bin=%0h got=%0h exp=%0h", binary, twos_comp, exp);

  // No X/Z on output when input is known
  assert property (@(binary or twos_comp) !$isunknown(binary) |-> !$isunknown(twos_comp))
    else $error("twos_complement X/Z on output while input is known");

  // Involution: ~~+1 on output returns input
  let inv = ((~twos_comp) + 4'd1)[3:0];
  assert property (@(binary or twos_comp) inv === binary)
    else $error("twos_complement involution failed: ~out+1 != in");

  // Arithmetic identity: b + (-b) == 0 (mod 16)
  assert property (@(binary or twos_comp) ((binary + twos_comp) & 4'hF) == 4'h0)
    else $error("twos_complement sum != 0 mod 16");

  // Functional coverage: all 16 input mappings seen and correct
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : cov_map
      localparam logic [3:0] I = i[3:0];
      localparam logic [3:0] E = ((~I) + 4'd1)[3:0];
      cover property (@(binary) (binary == I) && (twos_comp === E));
    end
  endgenerate

endmodule

bind twos_complement twos_complement_sva sva_twos_complement (.*);

`endif