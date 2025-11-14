// SVA checkers and binds for LUT3 and mux

// Checker for LUT3
module LUT3_sva (
  input logic I0, I1, I2, O
);
  // Functional correctness (check after delta to avoid races)
  property p_lut3_func;
    @(posedge I0 or negedge I0 or
      posedge I1 or negedge I1 or
      posedge I2 or negedge I2)
      ##0 O === ~(I0 & I1 & I2);
  endproperty
  assert property (p_lut3_func);

  // No X/Z on ports when they toggle
  assert property (@(posedge I0 or negedge I0 or
                     posedge I1 or negedge I1 or
                     posedge I2 or negedge I2)
                   !$isunknown({I0,I1,I2,O}));
endmodule

bind LUT3 LUT3_sva lut3_chk (.I0(I0), .I1(I1), .I2(I2), .O(O));

// Checker for mux (verifies wiring, functionality, X-checks, and coverage)
module mux_sva (
  input  logic       ctrl, D0, D1, S,
  input  logic [2:0] lut_input,
  input  logic       lut_output,
  input  logic       lut_i0, lut_i1, lut_i2, lut_o
);
  // Top-level functional equivalence to underlying NAND3 implemented by LUT3
  property p_mux_func;
    @(posedge ctrl or negedge ctrl or
      posedge D0   or negedge D0   or
      posedge D1   or negedge D1)
      ##0 S === ~(D1 & ctrl & D0);
  endproperty
  assert property (p_mux_func);

  // Wiring/connection checks
  assert property (@(posedge ctrl or negedge ctrl or
                     posedge D0   or negedge D0   or
                     posedge D1   or negedge D1   or
                     posedge S    or negedge S)
                   ##0 S === lut_output);

  assert property (@(posedge ctrl or negedge ctrl or
                     posedge D0   or negedge D0   or
                     posedge D1   or negedge D1)
                   ##0 {lut_input[2], lut_input[1], lut_input[0]} === {D0, ctrl, D1});

  // Instance port mapping checks
  assert property (@(posedge ctrl or negedge ctrl or
                     posedge D0   or negedge D0   or
                     posedge D1   or negedge D1)
                   ##0 (lut_i0 === lut_input[0] &&
                        lut_i1 === lut_input[1] &&
                        lut_i2 === lut_input[2] &&
                        lut_o  === lut_output));

  // No X/Z on ports when they toggle
  assert property (@(posedge ctrl or negedge ctrl or
                     posedge D0   or negedge D0   or
                     posedge D1   or negedge D1   or
                     posedge S    or negedge S)
                   !$isunknown({ctrl,D0,D1,S}));

  // Functional coverage: all input combinations seen at the mux boundary
  cover property (@(posedge ctrl or negedge ctrl or posedge D0 or negedge D0 or posedge D1 or negedge D1) ##0 {D1,ctrl,D0} == 3'b000);
  cover property (@(posedge ctrl or negedge ctrl or posedge D0 or negedge D0 or posedge D1 or negedge D1) ##0 {D1,ctrl,D0} == 3'b001);
  cover property (@(posedge ctrl or negedge ctrl or posedge D0 or negedge D0 or posedge D1 or negedge D1) ##0 {D1,ctrl,D0} == 3'b010);
  cover property (@(posedge ctrl or negedge ctrl or posedge D0 or negedge D0 or posedge D1 or negedge D1) ##0 {D1,ctrl,D0} == 3'b011);
  cover property (@(posedge ctrl or negedge ctrl or posedge D0 or negedge D0 or posedge D1 or negedge D1) ##0 {D1,ctrl,D0} == 3'b100);
  cover property (@(posedge ctrl or negedge ctrl or posedge D0 or negedge D0 or posedge D1 or negedge D1) ##0 {D1,ctrl,D0} == 3'b101);
  cover property (@(posedge ctrl or negedge ctrl or posedge D0 or negedge D0 or posedge D1 or negedge D1) ##0 {D1,ctrl,D0} == 3'b110);
  cover property (@(posedge ctrl or negedge ctrl or posedge D0 or negedge D0 or posedge D1 or negedge D1) ##0 {D1,ctrl,D0} == 3'b111);

  // Ensure both output values are exercised
  cover property (@(posedge ctrl or negedge ctrl or posedge D0 or negedge D0 or posedge D1 or negedge D1) ##0 S == 1'b0);
  cover property (@(posedge ctrl or negedge ctrl or posedge D0 or negedge D0 or posedge D1 or negedge D1) ##0 S == 1'b1);
endmodule

bind mux mux_sva mux_chk (
  .ctrl(ctrl), .D0(D0), .D1(D1), .S(S),
  .lut_input(lut_input), .lut_output(lut_output),
  .lut_i0(lut.I0), .lut_i1(lut.I1), .lut_i2(lut.I2), .lut_o(lut.O)
);