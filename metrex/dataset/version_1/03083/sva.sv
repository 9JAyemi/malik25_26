// SVA for decoder_3to8
// Bind this module or include alongside DUT

module decoder_3to8_sva (
  input  logic [2:0] in,
  input  logic [7:0] out
);
  // Sample on any change of in or out
  event ev;
  always @(in or out) -> ev;

  // Output is always known (no X/Z)
  ap_out_known: assert property (@(ev) !$isunknown(out))
    else $error("decoder_3to8: out has X/Z");

  // For known input: exact mapping and one-hot
  ap_map:    assert property (@(ev) !$isunknown(in) |-> out == (8'b1 << in))
    else $error("decoder_3to8: mapping mismatch for in=%0d", in);
  ap_onehot: assert property (@(ev) !$isunknown(in) |-> $onehot(out))
    else $error("decoder_3to8: out not one-hot for known in");

  // For unknown input: force zero
  ap_x2zero: assert property (@(ev) $isunknown(in) |-> out == 8'b0)
    else $error("decoder_3to8: unknown in must force out=0");

  // At most one bit set at all times
  ap_onehot0: assert property (@(ev) $onehot0(out))
    else $error("decoder_3to8: multiple bits set in out");

  // No spurious output changes when input is stable
  ap_no_glitch: assert property (@(ev) $stable(in) |-> $stable(out))
    else $error("decoder_3to8: out changed while in stable");

  // Functional coverage: hit each decode value
  cover property (@(ev) in==3'b000 && out==8'b00000001);
  cover property (@(ev) in==3'b001 && out==8'b00000010);
  cover property (@(ev) in==3'b010 && out==8'b00000100);
  cover property (@(ev) in==3'b011 && out==8'b00001000);
  cover property (@(ev) in==3'b100 && out==8'b00010000);
  cover property (@(ev) in==3'b101 && out==8'b00100000);
  cover property (@(ev) in==3'b110 && out==8'b01000000);
  cover property (@(ev) in==3'b111 && out==8'b10000000);

  // Optional: cover unknown-input path
  cover property (@(ev) $isunknown(in) && out==8'b0);

endmodule

// Bind example:
// bind decoder_3to8 decoder_3to8_sva u_decoder_3to8_sva (.in(in), .out(out));