// SVA for shift_mux
module shift_mux_sva (
  input logic [3:0] data_in,
  input logic [3:0] in_0, in_1, in_2, in_3,
  input logic [1:0]  sel,
  input logic        shift,
  input logic [3:0]  out,
  input logic [3:0]  shift_reg
);

  // Combinational mux correctness (4-state accurate)
  assert property ( (sel === 2'b00) -> (out == in_0) );
  assert property ( (sel === 2'b01) -> (out == in_1) );
  assert property ( (sel === 2'b10) -> (out == in_2) );
  assert property ( (sel === 2'b11) -> (out == in_3) );

  // If sel is X/Z, default branch to shift_reg
  assert property ( $isunknown(sel) -> (out == shift_reg) );

  // Out known when selected input is known
  assert property ( (sel===2'b00 && !$isunknown(in_0)) -> !$isunknown(out) );
  assert property ( (sel===2'b01 && !$isunknown(in_1)) -> !$isunknown(out) );
  assert property ( (sel===2'b10 && !$isunknown(in_2)) -> !$isunknown(out) );
  assert property ( (sel===2'b11 && !$isunknown(in_3)) -> !$isunknown(out) );

  // Shift register updates on posedge(shift)
  assert property (@(posedge shift)
    (!$isunknown($past(shift_reg))) |-> (shift_reg == {$past(shift_reg[2:0]), $past(data_in[3])})
  );

  // Shift register changes only on posedge(shift)
  assert property ( !$changed(shift_reg) or $rose(shift) );

  // Coverage
  cover property (sel===2'b00 && out==in_0);
  cover property (sel===2'b01 && out==in_1);
  cover property (sel===2'b10 && out==in_2);
  cover property (sel===2'b11 && out==in_3);
  cover property (@(posedge shift) 1);
  cover property (@(posedge shift) shift_reg == {$past(shift_reg[2:0]), $past(data_in[3])});
  cover property ($isunknown(sel) && out==shift_reg); // exercises default path

endmodule

// Bind into DUT
bind shift_mux shift_mux_sva sva_inst (.*);