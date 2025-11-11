// SVA for sine_lut — bindable, concise, and thorough on functionality
// Drive clk with any free-running TB clock; tie rst_n high if unused.

package sine_lut_sva_pkg;
  typedef logic [7:0] u8_t;

  // Golden LUT (addr 0..255 -> s)
  localparam u8_t L [256] = '{
    8'h80,8'h83,8'h86,8'h89,8'h8C,8'h8F,8'h92,8'h95,8'h98,8'h9B,8'h9E,8'hA2,8'hA5,8'hA7,8'hAA,8'hAD,
    8'hB0,8'hB3,8'hB6,8'hB9,8'hBC,8'hBE,8'hC1,8'hC4,8'hC6,8'hC9,8'hCB,8'hCE,8'hD0,8'hD3,8'hD5,8'hD7,
    8'hDA,8'hDC,8'hDE,8'hE0,8'hE2,8'hE4,8'hE6,8'hE8,8'hEA,8'hEB,8'hED,8'hEE,8'hF0,8'hF1,8'hF3,8'hF4,
    8'hF5,8'hF6,8'hF8,8'hF9,8'hFA,8'hFA,8'hFB,8'hFC,8'hFD,8'hFD,8'hFE,8'hFE,8'hFE,8'hFF,8'hFF,8'hFF,
    8'hFF,8'hFF,8'hFF,8'hFF,8'hFE,8'hFE,8'hFE,8'hFD,8'hFD,8'hFC,8'hFB,8'hFA,8'hFA,8'hF9,8'hF8,8'hF6,
    8'hF5,8'hF4,8'hF3,8'hF1,8'hF0,8'hEE,8'hED,8'hEB,8'hEA,8'hE8,8'hE6,8'hE4,8'hE2,8'hE0,8'hDE,8'hDC,
    8'hDA,8'hD7,8'hD5,8'hD3,8'hD0,8'hCE,8'hCB,8'hC9,8'hC6,8'hC4,8'hC1,8'hBE,8'hBC,8'hB9,8'hB6,8'hB3,
    8'hB0,8'hAD,8'hAA,8'hA7,8'hA5,8'hA2,8'h9E,8'h9B,8'h98,8'h95,8'h92,8'h8F,8'h8C,8'h89,8'h86,8'h83,
    8'h80,8'h7C,8'h79,8'h76,8'h73,8'h70,8'h6D,8'h6A,8'h67,8'h64,8'h61,8'h5D,8'h5A,8'h58,8'h55,8'h52,
    8'h4F,8'h4C,8'h49,8'h46,8'h43,8'h41,8'h3E,8'h3B,8'h39,8'h36,8'h34,8'h31,8'h2F,8'h2C,8'h2A,8'h28,
    8'h25,8'h23,8'h21,8'h1F,8'h1D,8'h1B,8'h19,8'h17,8'h15,8'h14,8'h12,8'h11,8'h0F,8'h0E,8'h0C,8'h0B,
    8'h0A,8'h09,8'h07,8'h06,8'h05,8'h05,8'h04,8'h03,8'h02,8'h02,8'h01,8'h01,8'h01,8'h00,8'h00,8'h00,
    8'h00,8'h00,8'h00,8'h00,8'h01,8'h01,8'h01,8'h02,8'h02,8'h03,8'h04,8'h05,8'h05,8'h06,8'h07,8'h09,
    8'h0A,8'h0B,8'h0C,8'h0E,8'h0F,8'h11,8'h12,8'h14,8'h15,8'h17,8'h19,8'h1B,8'h1D,8'h1F,8'h21,8'h23,
    8'h25,8'h28,8'h2A,8'h2C,8'h2F,8'h31,8'h34,8'h36,8'h39,8'h3B,8'h3E,8'h41,8'h43,8'h46,8'h49,8'h4C,
    8'h4F,8'h52,8'h55,8'h58,8'h5A,8'h5D,8'h61,8'h64,8'h67,8'h6A,8'h6D,8'h70,8'h73,8'h76,8'h79,8'h7C
  };
endpackage

module sine_lut_sva
(
  input  logic        clk,
  input  logic        rst_n,
  input  logic [7:0]  addr,
  input  logic [7:0]  s
);
  import sine_lut_sva_pkg::*;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // X/Z checks
  a_no_x_addr: assert property (!$isunknown(addr));
  a_no_x_s:    assert property (!$isunknown(s));

  // Functional correctness: exact LUT mapping
  a_lut_match: assert property (s == L[addr]);

  // No spurious output activity when input is stable
  a_stable_out_when_stable_in: assert property ($stable(addr) |-> $stable(s));
  a_out_changes_only_on_in:    assert property ($changed(s) |-> $changed(addr));

  // Minimal yet complete coverage
  covergroup cg @(posedge clk);
    option.per_instance = 1;
    coverpoint addr { bins all[] = {[0:255]}; } // hit every address
    coverpoint s    { bins min = {8'h00}; bins mid = {8'h80}; bins max = {8'hFF}; }
  endgroup
  cg cg_i = new();

endmodule

// Bind example (hook up your TB clock/reset)
// bind sine_lut sine_lut_sva u_sine_lut_sva (.clk(tb_clk), .rst_n(tb_rst_n), .addr(addr), .s(s));