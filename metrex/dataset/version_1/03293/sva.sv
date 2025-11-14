// SVA for top_module, barrel_shifter_16bit, and alu
// Uses event-based sampling (no external clock required)

module top_module_sva;
  // Sample on any combinational activity relevant to top_module
  event ev;
  always @* -> ev;

  // Local reference models
  function automatic [3:0] alu_ref(input [3:0] a, input [3:0] b, input [1:0] op);
    case (op)
      2'b00: alu_ref = a & b;
      2'b01: alu_ref = a | b;
      2'b10: alu_ref = a + b;
      2'b11: alu_ref = a - b;
    endcase
  endfunction

  function automatic [15:0] shifter_ref(input [15:0] din, input [2:0] shamt, input bit mode);
    shifter_ref = mode ? (din << shamt) : din;
  endfunction

  // No unknowns on outputs
  assert property (@(ev) !$isunknown({result, valid}));

  // ALU valid should always be 1 (propagated from alu_inst)
  assert property (@(ev) valid == 1'b1);

  // Result mux correctness per control[3:0]
  assert property (@(ev) (control == 4'b0000) |-> (result == A));
  assert property (@(ev) (control == 4'b0001) |-> (result == B));
  assert property (@(ev) (control == 4'b0010) |-> (result == (A + B)));
  assert property (@(ev) (control == 4'b0011) |-> (result == (A - B)));
  assert property (@(ev) (control == 4'b0100) |-> (result == shifter_ref(A, control[2:0], control[3])));
  assert property (@(ev) (control == 4'b0101) |-> (result == {12'h000, alu_ref(B[3:0], B[7:4], control[1:0])}));
  assert property (@(ev) (control == 4'b0110) |-> (result == (A & B)));
  assert property (@(ev) (control == 4'b0111) |-> (result == (A | B)));
  assert property (@(ev) (control == 4'b1000) |-> (result ==
                             (shifter_ref(A, control[2:0], control[3]) &
                              {12'h000, alu_ref(B[3:0], B[7:4], control[1:0])})));
  // Default branch: control[3]==1 and control[2:0]!=000 -> result == 0
  assert property (@(ev) (control[3] && (control[2:0] != 3'b000)) |-> (result == 16'h0000));

  // Functional coverage: cover each mux selection and default-space
  cover property (@(ev) control == 4'b0000);
  cover property (@(ev) control == 4'b0001);
  cover property (@(ev) control == 4'b0010);
  cover property (@(ev) control == 4'b0011);
  cover property (@(ev) control == 4'b0100);
  cover property (@(ev) control == 4'b0101);
  cover property (@(ev) control == 4'b0110);
  cover property (@(ev) control == 4'b0111);
  cover property (@(ev) control == 4'b1000);
  cover property (@(ev) (control[3] && (control[2:0] != 3'b000))); // default space
endmodule

bind top_module top_module_sva tm_sva();

// -----------------------------------------------------------------------------

module barrel_shifter_16bit_sva;
  // Sample on any combinational activity relevant to shifter
  event ev;
  always @* -> ev;

  // Reference behavior
  function automatic [15:0] shifter_ref(input [15:0] din, input [2:0] shamt, input bit mode);
    shifter_ref = mode ? (din << shamt) : din;
  endfunction

  // Correct output
  assert property (@(ev) shifted_out == shifter_ref(data_in, shift_amount, mode));

  // No unknowns
  assert property (@(ev) !$isunknown(shifted_out));

  // Coverage: mode 0 passthrough, and each shift amount when mode=1
  cover property (@(ev) (mode == 1'b0) && (shifted_out == data_in));
  cover property (@(ev) (mode == 1'b1) && (shift_amount == 3'd0));
  cover property (@(ev) (mode == 1'b1) && (shift_amount == 3'd1));
  cover property (@(ev) (mode == 1'b1) && (shift_amount == 3'd2));
  cover property (@(ev) (mode == 1'b1) && (shift_amount == 3'd3));
  cover property (@(ev) (mode == 1'b1) && (shift_amount == 3'd4));
  cover property (@(ev) (mode == 1'b1) && (shift_amount == 3'd5));
  cover property (@(ev) (mode == 1'b1) && (shift_amount == 3'd6));
  cover property (@(ev) (mode == 1'b1) && (shift_amount == 3'd7));
endmodule

bind barrel_shifter_16bit barrel_shifter_16bit_sva sh_sva();

// -----------------------------------------------------------------------------

module alu_sva;
  // Sample on any combinational activity relevant to ALU
  event ev;
  always @* -> ev;

  // Correct result per op
  assert property (@(ev) (op == 2'b00) |-> (result == (A & B)));
  assert property (@(ev) (op == 2'b01) |-> (result == (A | B)));
  assert property (@(ev) (op == 2'b10) |-> (result == (A + B)));
  assert property (@(ev) (op == 2'b11) |-> (result == (A - B)));

  // Valid is always 1 and outputs known
  assert property (@(ev) valid == 1'b1);
  assert property (@(ev) !$isunknown({result, valid}));

  // Coverage: each ALU op
  cover property (@(ev) op == 2'b00);
  cover property (@(ev) op == 2'b01);
  cover property (@(ev) op == 2'b10);
  cover property (@(ev) op == 2'b11);
endmodule

bind alu alu_sva alu_sva_i();