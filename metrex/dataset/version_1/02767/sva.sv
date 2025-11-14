// SVA checker for flt_fx_24p8
module flt_fx_24p8_sva
(
  input  logic        clk,
  input  logic        rst_n,
  input  logic [31:0] fp_in,
  input  logic [31:0] int_out
);

  // Reference model (matches DUT intent)
  function automatic logic [31:0] golden(input logic [31:0] fp);
    logic [7:0]  bias_exp, bias_exp2;
    logic [47:0] bias_mant, int_fixed_out;
    logic [31:0] fixed_out;
    begin
      bias_mant    = {25'h0001, fp[22:0]};
      bias_exp     = fp[30:23] - 8'd127;
      bias_exp2    = ~bias_exp + 8'h1;
      if (fp[30:0] == 31'b0)      int_fixed_out = '0;
      else if (bias_exp[7])       int_fixed_out = bias_mant >> bias_exp2;
      else                        int_fixed_out = bias_mant << bias_exp;
      fixed_out    = int_fixed_out[46:15];
      golden       = fp[31] ? (~fixed_out + 32'd1) : fixed_out;
    end
  endfunction

  default clocking @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Functional equivalence (single-cycle comb)
  a_func_eq: assert property (int_out == golden(fp_in));

  // Zero handling
  a_zero:    assert property ((fp_in[30:0] == 31'b0) |-> (int_out == 32'b0));

  // Sign handling (non-zero result has same sign as input)
  a_sign:    assert property ((fp_in[30:0] != 31'b0 && int_out != 32'b0) |-> (int_out[31] == fp_in[31]));

  // INF/NaN (E==255) behavior per DUT (drives 0)
  a_inf_nan: assert property ((fp_in[30:23] == 8'hFF) |-> (int_out == 32'b0));

  // No X/Z propagation when input is clean
  a_no_x:    assert property ((!$isunknown(fp_in)) |-> (!$isunknown(int_out)));

  // Basic stability: if input stable over a cycle, output stable too
  a_stable:  assert property ($stable(fp_in) |-> $stable(int_out));

  // ------------- Coverage -------------

  // Zero
  c_zero:           cover property (fp_in[30:0] == 31'b0);

  // Sign coverage (non-zero magnitude)
  c_pos:            cover property (fp_in[31] == 1'b0 && fp_in[30:0] != 0);
  c_neg:            cover property (fp_in[31] == 1'b1 && fp_in[30:0] != 0);

  // Subnormal
  c_subnormal:      cover property (fp_in[30:23] == 8'h00 && fp_in[22:0] != 0);

  // Normal exponent shifting paths
  c_rshift_path:    cover property (fp_in[30:0] != 0 && (fp_in[30:23]-8'd127)[7]);
  c_lshift_path:    cover property (fp_in[30:0] != 0 && !((fp_in[30:23]-8'd127)[7]) && fp_in[30:23] != 8'hFF);

  // Exact zero shift (E==127)
  c_zero_shift:     cover property (fp_in[30:23] == 8'd127);

  // Large shifts
  c_large_rshift:   cover property (fp_in[30:0] != 0 && (fp_in[30:23]-8'd127)[7] &&
                                    ((~(fp_in[30:23]-8'd127)+8'd1) >= 8'd31));
  c_large_lshift:   cover property (fp_in[30:0] != 0 && !((fp_in[30:23]-8'd127)[7]) &&
                                    ((fp_in[30:23]-8'd127) >= 8'd31));

  // INF / NaN
  c_inf:            cover property (fp_in[30:23] == 8'hFF && fp_in[22:0] == 0);
  c_nan:            cover property (fp_in[30:23] == 8'hFF && fp_in[22:0] != 0);

endmodule

// Example bind (provide clk/rst_n from your environment)
// bind flt_fx_24p8 flt_fx_24p8_sva u_flt_fx_24p8_sva(.clk(clk), .rst_n(rst_n), .fp_in(fp_in), .int_out(int_out));