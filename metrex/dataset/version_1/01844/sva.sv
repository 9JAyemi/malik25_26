// SystemVerilog Assertions (SVA) for the provided design.
// Bind these to the DUT; no DUT edits required.

// -----------------------------------------------------------------------------
// combinational_logic
// -----------------------------------------------------------------------------
module combinational_logic_sva (
  input  logic [2:0] vec,
  input  logic       out1,
  input  logic       out2,
  input  logic       out3
);
  // Pure combinational mapping (4-state exact)
  always @* begin
    assert (out1 === vec[0]) else $error("comb: out1 != vec[0]");
    assert (out2 === vec[1]) else $error("comb: out2 != vec[1]");
    assert (out3 === vec[2]) else $error("comb: out3 != vec[2]");
  end
endmodule

bind combinational_logic combinational_logic_sva comb_sva (
  .vec (vec),
  .out1(out1),
  .out2(out2),
  .out3(out3)
);

// -----------------------------------------------------------------------------
// shift_register
// -----------------------------------------------------------------------------
module shift_register_sva (
  input  logic       clk,
  input  logic       serial_in,
  input  logic       serial_out,
  // bind to internal shift_reg for a precise check of implementation intent
  input  logic [2:0] shift_reg
);
  default clocking cb @(posedge clk); endclocking

  // serial_out is the pre-shift MSB (matches blocking assignment with NBA update)
  assert property (serial_out == $past(shift_reg[2]))
    else $error("shift: serial_out != old MSB (pre-shift)");

  // 3-cycle pipeline behavior after fill: serial_out == serial_in delayed by 3
  assert property ($past($rose(clk),3) |-> serial_out == $past(serial_in,3))
    else $error("shift: serial_out != serial_in delayed by 3");

  // No mid-cycle glitches (basic check at negedge)
  assert property (@(negedge clk) $stable(serial_out))
    else $error("shift: serial_out changed between clocks");

  // Simple toggle coverage
  cover property ($rose(serial_out));
  cover property ($fell(serial_out));
endmodule

bind shift_register shift_register_sva sr_sva (
  .clk       (clk),
  .serial_in (serial_in),
  .serial_out(serial_out),
  .shift_reg (shift_reg)
);

// -----------------------------------------------------------------------------
// functional_module
// -----------------------------------------------------------------------------
module functional_module_sva (
  input  logic       in1,
  input  logic       in2,
  input  logic       in3,
  input  logic       serial_out,
  input  logic [3:0] final_output
);
  // Exact concatenation (4-state exact)
  always @* begin
    assert (final_output === {in1,in2,in3,serial_out})
      else $error("func: final_output != {in1,in2,in3,serial_out}");
  end
endmodule

bind functional_module functional_module_sva func_sva (
  .in1          (in1),
  .in2          (in2),
  .in3          (in3),
  .serial_out   (serial_out),
  .final_output (final_output)
);

// -----------------------------------------------------------------------------
// top_module
// -----------------------------------------------------------------------------
module top_module_sva (
  input  logic       clk,
  input  logic [2:0] vec,
  input  logic       serial_in,
  input  logic       serial_out,
  input  logic [3:0] final_output
);
  default clocking cb @(posedge clk); endclocking

  // End-to-end composition check
  assert property (final_output === {vec[0], vec[1], vec[2], serial_out})
    else $error("top: final_output composition mismatch");

  // End-to-end 3-cycle behavior on LSB (after pipeline fill)
  assert property ($past($rose(clk),3) |-> final_output[0] == $past(serial_in,3))
    else $error("top: final_output[0] != serial_in delayed by 3");

  // Full vec-space coverage
  cover property (vec == 3'b000);
  cover property (vec == 3'b001);
  cover property (vec == 3'b010);
  cover property (vec == 3'b011);
  cover property (vec == 3'b100);
  cover property (vec == 3'b101);
  cover property (vec == 3'b110);
  cover property (vec == 3'b111);
endmodule

bind top_module top_module_sva top_sva (
  .clk         (clk),
  .vec         (vec),
  .serial_in   (serial_in),
  .serial_out  (serial_out),
  .final_output(final_output)
);