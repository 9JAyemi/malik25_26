// SVA for shift_register
// Focused, high-quality checks + concise coverage

`ifndef SHIFT_REGISTER_SVA
`define SHIFT_REGISTER_SVA

module shift_register_sva(
  input logic clk,
  input logic load,
  input logic serial_in,
  input logic [2:0] out
);

  default clocking cb @(posedge clk); endclocking

  // history valid qualifiers for $past depth
  bit pv1, pv2, pv3;
  initial begin pv1=0; pv2=0; pv3=0; end
  always_ff @(posedge clk) begin
    pv1 <= 1'b1;
    pv2 <= pv1;
    pv3 <= pv2;
  end

  // Sanity: no X/Z on key signals
  assert property (!$isunknown({load, serial_in}))) else $error("X/Z on inputs");
  assert property (!$isunknown(out)) else $error("X/Z on out");

  // Functional correctness
  // On load: out <= zero-extended serial_in
  assert property (disable iff (!pv1) load |=> out == {2'b00, $past(serial_in)})
    else $error("Load behavior mismatch");

  // On shift: out <= {out[1:0], serial_in}
  assert property (disable iff (!pv1) !load |=> out == {$past(out[1:0]), $past(serial_in)})
    else $error("Shift behavior mismatch");

  // After three consecutive shifts, out equals last three serial_in samples
  assert property (disable iff (!pv3) (!load ##1 !load ##1 !load)
                   |=> out == {$past(serial_in,3), $past(serial_in,2), $past(serial_in,1)})
    else $error("3-shift streaming mismatch");

  // Load then one shift: MSB forced 0, lower bits are serial_in history
  assert property (disable iff (!pv2) (load ##1 !load)
                   |=> out == {1'b0, $past(serial_in,2), $past(serial_in,1)})
    else $error("Load->shift compose mismatch");

  // Minimal but meaningful coverage
  cover property (load);
  cover property (!load);
  cover property (!load ##1 !load ##1 !load);     // 3 consecutive shifts
  cover property (load ##1 !load ##1 !load);       // load then shift twice
  cover property (out == 3'b000);
  cover property (out == 3'b111);

endmodule

bind shift_register shift_register_sva sva_i (
  .clk(clk),
  .load(load),
  .serial_in(serial_in),
  .out(out)
);

`endif