// SVA for shift_reg_mux_adder
// Bind into the DUT to access internal signals
module shift_reg_mux_adder_sva;
  // helper: extract selected byte from 256-bit input
  function automatic logic [7:0] byte_at(input logic [255:0] v, input logic [7:0] s);
    byte_at = v[8*s +: 8];
  endfunction

  // Shift-register correctness (guard first cycle/unknowns)
  property p_shift;
    @(posedge clk)
      (!$isunknown($past({shift_reg[1:0], d})))
      |-> shift_reg == { $past(shift_reg[1:0]), $past(d) };
  endproperty
  assert property (p_shift) else $error("shift_reg shift behavior mismatch");

  // Barrel shifter: in-range select => selected byte
  property p_barrel_inrange;
    @(posedge clk)
      (!$isunknown(sel) && sel <= 8'h1F && !$isunknown(byte_at(in, sel)))
      |-> shifted_in == byte_at(in, sel);
  endproperty
  assert property (p_barrel_inrange) else $error("Barrel select mismatch for sel in-range");

  // Barrel shifter: default on out-of-range or unknown sel => zero
  property p_barrel_default;
    @(posedge clk)
      ($isunknown(sel) || sel > 8'h1F) |-> shifted_in == 8'h00;
  endproperty
  assert property (p_barrel_default) else $error("Barrel default mismatch");

  // Mux passthrough
  property p_mux_passthru;
    @(posedge clk)
      (!$isunknown(shifted_in)) |-> mux_out == shifted_in;
  endproperty
  assert property (p_mux_passthru) else $error("mux_out != shifted_in");

  // Indexed bit select: reg_out equals selected bit of mux_out
  property p_index_select;
    @(posedge clk)
      (!$isunknown(shift_reg[2:0]) && !$isunknown(mux_out))
      |-> reg_out == mux_out[shift_reg[2:0]];
  endproperty
  assert property (p_index_select) else $error("reg_out bit-select mismatch");

  // Adder truncation: out is XOR of reg_out and shift_reg[2]
  property p_adder_trunc;
    @(posedge clk)
      (!$isunknown({reg_out, shift_reg[2]}))
      |-> out == (reg_out ^ shift_reg[2]);
  endproperty
  assert property (p_adder_trunc) else $error("Adder/XOR relation mismatch");

  // Out must be known when all contributors are known and sel in-range
  property p_out_known_when_inputs_known;
    @(posedge clk)
      (!$isunknown(shift_reg) && !$isunknown(sel) && sel <= 8'h1F &&
       !$isunknown(byte_at(in, sel)))
      |-> !$isunknown(out);
  endproperty
  assert property (p_out_known_when_inputs_known) else $error("out is X with well-defined inputs");

  // Coverage
  // - All 32 byte selects exercised
  genvar si;
  generate
    for (si = 0; si < 32; si++) begin : C_SEL_BYTES
      cover property (@(posedge clk) sel == si[7:0]);
    end
  endgenerate

  // - Default path (unknown or out-of-range sel)
  cover property (@(posedge clk) ($isunknown(sel) || sel > 8'h1F) && shifted_in == 8'h00);

  // - All 8 index values exercised for bit-select
  genvar bi;
  generate
    for (bi = 0; bi < 8; bi++) begin : C_IDX_BITS
      cover property (@(posedge clk) shift_reg[2:0] == bi[2:0]);
    end
  endgenerate

  // - Both XOR outcomes
  cover property (@(posedge clk) out == 1'b0);
  cover property (@(posedge clk) out == 1'b1);
endmodule

bind shift_reg_mux_adder shift_reg_mux_adder_sva sva_i();