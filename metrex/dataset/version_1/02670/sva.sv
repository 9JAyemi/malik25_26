// SVA for barrel_shift_mux
// Bind these assertions to the DUT. Provide a clock/reset from your TB.

module barrel_shift_mux_sva (
  input logic                 clk,
  input logic                 rst_n,

  input logic [7:0]           data_in0,
  input logic [7:0]           data_in1,
  input logic [7:0]           data_in2,
  input logic [7:0]           data_in3,
  input logic [1:0]           select,
  input logic                 shift_left,
  input logic                 shift_right,
  input logic                 rotate_right,
  input logic [7:0]           data_out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  function automatic logic [7:0] shifter_expected (
    input logic [7:0] d0,
    input logic sl, sr, rr
  );
    unique case ({sl,sr,rr})
      3'b001: shifter_expected = {d0[6:0], 1'b0};        // left shift by 1
      3'b010: shifter_expected = {1'b0, d0[7:1]};        // right shift by 1
      3'b100: shifter_expected = {d0[0], d0[7:1]};       // rotate right by 1
      default: shifter_expected = d0;                     // pass-through
    endcase
  endfunction

  // Functional equivalence of the whole module
  assert property (
    data_out ==
      (select == 2'b00 ? shifter_expected(data_in0, shift_left, shift_right, rotate_right) :
       select == 2'b01 ? data_in1 :
       select == 2'b10 ? data_in2 :
                         data_in3)
  ) else $error("barrel_shift_mux: data_out mismatch");

  // X-propagation sanity: no X on output if all controls and selected data are known
  assert property (
    // all inputs known
    !$isunknown({select, shift_left, shift_right, rotate_right,
                 data_in0, data_in1, data_in2, data_in3})
    |-> !$isunknown(data_out)
  ) else $error("barrel_shift_mux: data_out is X/Z while inputs are known");

  // Targeted checks on shifter path when selected
  assert property (
    select == 2'b00 && {shift_left,shift_right,rotate_right} == 3'b001
    |-> data_out == {data_in0[6:0], 1'b0}
  ) else $error("barrel_shift_mux: left-shift case failed");

  assert property (
    select == 2'b00 && {shift_left,shift_right,rotate_right} == 3'b010
    |-> data_out == {1'b0, data_in0[7:1]}
  ) else $error("barrel_shift_mux: right-shift case failed");

  assert property (
    select == 2'b00 && {shift_left,shift_right,rotate_right} == 3'b100
    |-> data_out == {data_in0[0], data_in0[7:1]}
  ) else $error("barrel_shift_mux: rotate-right case failed");

  assert property (
    select == 2'b00 &&
    ({shift_left,shift_right,rotate_right} inside {3'b000,3'b011,3'b101,3'b110,3'b111})
    |-> data_out == data_in0
  ) else $error("barrel_shift_mux: default pass-through failed");

  // Functional coverage
  cover property (select == 2'b00);
  cover property (select == 2'b01);
  cover property (select == 2'b10);
  cover property (select == 2'b11);

  cover property (select == 2'b00 && {shift_left,shift_right,rotate_right} == 3'b001);
  cover property (select == 2'b00 && {shift_left,shift_right,rotate_right} == 3'b010);
  cover property (select == 2'b00 && {shift_left,shift_right,rotate_right} == 3'b100);
  cover property (select == 2'b00 && {shift_left,shift_right,rotate_right} == 3'b000);
  cover property (select == 2'b00 && (shift_left + shift_right + rotate_right) >= 2);

endmodule

// Bind example (map clk/rst_n from your TB scope)
bind barrel_shift_mux barrel_shift_mux_sva sva (
  .clk      (clk),
  .rst_n    (rst_n),
  .data_in0 (data_in0),
  .data_in1 (data_in1),
  .data_in2 (data_in2),
  .data_in3 (data_in3),
  .select   (select),
  .shift_left  (shift_left),
  .shift_right (shift_right),
  .rotate_right(rotate_right),
  .data_out (data_out)
);