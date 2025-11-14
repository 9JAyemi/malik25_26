// SVA checkers and binds for the provided RTL

// Checker for top_module
module top_module_sva (
  input  logic        clk,
  input  logic [11:0] in,
  input  logic [7:0]  out,
  input  logic [3:0]  lower,
  input  logic [3:0]  middle,
  input  logic [3:0]  upper,
  input  logic [2:0]  shift_reg,
  input  logic [2:0]  rotated_lower,
  input  logic [11:0] shifted_in,
  input  logic [11:0] and_out
);
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Slice sanity (structural)
  a_lower:  assert property (lower  == in[3:0]);
  a_middle: assert property (middle == in[7:4]);
  a_upper:  assert property (upper  == in[11:8]);

  // Actual sequential behavior due to width truncation
  a_shift_reg_actual: assert property (past_valid |-> shift_reg == $past(in[2:0]));

  // Rotated lower equals shift_reg (as coded)
  a_rot_eq_sr: assert property (rotated_lower == shift_reg);

  // Concatenation width effect (MSB forced 0) and field mapping
  a_shiftedin_msb0:     assert property (shifted_in[11] == 1'b0);
  a_shiftedin_mapping:  assert property ({shifted_in[10:8], shifted_in[7:4], shifted_in[3:0]} ==
                                          {rotated_lower,     middle,          upper});

  // AND and output correctness
  a_and_eq: assert property (and_out == (shifted_in & in));
  a_out_eq: assert property (out == and_out[7:0] && out == ((shifted_in & in)[7:0]));

  // No X on outputs
  a_no_x_out: assert property (!$isunknown(out));

  // Coverage
  genvar v;
  generate
    for (v=0; v<8; v++) begin : g_cov_sr
      c_sr_val: cover property (shift_reg == v[2:0]);
    end
  endgenerate
  c_out_zero:  cover property (out == 8'h00);
  c_out_nz:    cover property (out != 8'h00);
  c_msb1_never: cover property (shifted_in[11] == 1'b1); // should remain uncovered with current RTL
endmodule

// Checker for barrel_shifter
module barrel_shifter_sva (
  input logic [11:0] in,
  input logic [1:0]  shift,
  input logic [11:0] out
);
  logic [11:0] ref;
  always_comb begin
    ref = shift[1]
          ? {in[7:0], in[11:8], in[3:0]}[11:0]
          : {in[3:0], in[7:4], in[11:8], (in[10:4] >> shift[0])}[11:0];
  end
  a_eq:     assert property (@*) out == ref;
  c_s00:    cover  property (@*) (shift == 2'b00);
  c_s01:    cover  property (@*) (shift == 2'b01);
  c_s10:    cover  property (@*) (shift == 2'b10);
  c_s11:    cover  property (@*) (shift == 2'b11);
endmodule

// Checker for and_gate
module and_gate_sva (
  input logic [11:0] in1,
  input logic [11:0] in2,
  input logic [11:0] out
);
  a_and: assert property (@*) out == (in1 & in2);
  c_zero: cover property (@*) out == 12'h000;
  c_all1: cover property (@*) out == 12'hFFF;
endmodule

// Binds
bind top_module     top_module_sva     u_top_sva (.clk(clk), .in(in), .out(out),
                                                  .lower(lower), .middle(middle), .upper(upper),
                                                  .shift_reg(shift_reg), .rotated_lower(rotated_lower),
                                                  .shifted_in(shifted_in), .and_out(and_out));
bind barrel_shifter barrel_shifter_sva u_bs_sva   (.*);
bind and_gate       and_gate_sva       u_and_sva  (.*);