// SVA checker for ctrl_module (combinational), with bind
module ctrl_module_sva (
  input  logic [3:0] in,
  input  logic [1:0] ctrl,
  input  logic [3:0] out,
  input  logic [2:0] index
);

  // Immediate assertions in reactive region avoid delta-scheduling races
  always_comb begin
    // No X/Z on driving inputs used by logic; no X/Z on out
    assert (!$isunknown({ctrl, in[1:0]})) else $error("X/Z on ctrl or in[1:0]");
    assert (!$isunknown(out))            else $error("X/Z on out");

    // Internal index must equal concatenation {ctrl, in[1:0]}
    assert (index == {ctrl, in[1:0]})    else $error("index != {ctrl,in[1:0]}");

    // Functional truth table
    unique case ({ctrl, in[1:0]})
      3'b000: assert (out == 4'b0000) else $error("map 000 -> 0000 failed");
      3'b001: assert (out == 4'b1010) else $error("map 001 -> 1010 failed");
      3'b010: assert (out == 4'b0101) else $error("map 010 -> 0101 failed");
      3'b011: assert (out == 4'b1111) else $error("map 011 -> 1111 failed");
      3'b100: assert (out == 4'b1110) else $error("map 100 -> 1110 failed");
      3'b101: assert (out == 4'b0101) else $error("map 101 -> 0101 failed");
      3'b110: assert (out == 4'b1010) else $error("map 110 -> 1010 failed");
      3'b111: assert (out == 4'b0000) else $error("map 111 -> 0000 failed");
    endcase
  end

  // High input bits [3:2] must not affect out
  property hi_bits_irrelevant;
    @(in[3] or in[2]) $stable({ctrl, in[1:0]}) |-> $stable(out);
  endproperty
  assert property (hi_bits_irrelevant);

  // Coverage: hit all 8 input combinations with correct output
  cover property (@(in or ctrl) {ctrl, in[1:0]}==3'b000 && out==4'b0000);
  cover property (@(in or ctrl) {ctrl, in[1:0]}==3'b001 && out==4'b1010);
  cover property (@(in or ctrl) {ctrl, in[1:0]}==3'b010 && out==4'b0101);
  cover property (@(in or ctrl) {ctrl, in[1:0]}==3'b011 && out==4'b1111);
  cover property (@(in or ctrl) {ctrl, in[1:0]}==3'b100 && out==4'b1110);
  cover property (@(in or ctrl) {ctrl, in[1:0]}==3'b101 && out==4'b0101);
  cover property (@(in or ctrl) {ctrl, in[1:0]}==3'b110 && out==4'b1010);
  cover property (@(in or ctrl) {ctrl, in[1:0]}==3'b111 && out==4'b0000);

  // Coverage: see all unique output values
  cover property (@(in or ctrl) out==4'b0000);
  cover property (@(in or ctrl) out==4'b1010);
  cover property (@(in or ctrl) out==4'b0101);
  cover property (@(in or ctrl) out==4'b1111);
  cover property (@(in or ctrl) out==4'b1110);

endmodule

bind ctrl_module ctrl_module_sva sva_ctrl_module (
  .in(in), .ctrl(ctrl), .out(out), .index(index)
);