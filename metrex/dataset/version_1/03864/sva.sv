// SVA for flt2int
// Bind this checker to the DUT to verify combinational mapping and the registered output.
// Focused, high-quality assertions plus concise but meaningful coverage.

module flt2int_sva (
  input logic        clk,
  input logic [31:0] afl,
  input logic [15:0] fx_int,
  input logic [14:0] int_out
);
  default clocking cb @ (posedge clk); endclocking

  // Expected combinational mapping of int_out from afl[30:23] and afl[22:0]
  function automatic logic [14:0] calc_int_out (input logic [31:0] a);
    logic [7:0] e;
    begin
      e = a[30:23];
      if (e == 8'h7f) calc_int_out = 15'h0001;
      else begin
        casex (e)
          8'b0xxx_xxxx: calc_int_out = 15'h0000;
          8'h80:        calc_int_out = {14'h0001, a[22]};
          8'h81:        calc_int_out = {13'h0001, a[22:21]};
          8'h82:        calc_int_out = {12'h0001, a[22:20]};
          8'h83:        calc_int_out = {11'h0001, a[22:19]};
          8'h84:        calc_int_out = {10'h0001, a[22:18]};
          8'h85:        calc_int_out = { 9'h0001, a[22:17]};
          8'h86:        calc_int_out = { 8'h01,   a[22:16]};
          8'h87:        calc_int_out = { 7'h01,   a[22:15]};
          8'h88:        calc_int_out = { 6'h01,   a[22:14]};
          8'h89:        calc_int_out = { 5'h01,   a[22:13]};
          8'h8a:        calc_int_out = { 4'h1,    a[22:12]};
          8'h8b:        calc_int_out = { 3'h1,    a[22:11]};
          8'h8c:        calc_int_out = { 2'h1,    a[22:10]};
          8'h8d:        calc_int_out = { 1'h1,    a[22: 9]};
          default:      calc_int_out = 15'h7fff;
        endcase
      end
    end
  endfunction

  function automatic logic [15:0] calc_fx (input logic [31:0] a);
    logic [14:0] m;
    begin
      m = calc_int_out(a);
      calc_fx = a[31] ? ( {1'b0, ~m} + 16'h0001 ) : {1'b0, m};
    end
  endfunction

  // Sanity: inputs are known
  a_no_x_inputs: assert property ( !$isunknown(afl) )
    else $error("flt2int: afl has X/Z");

  // Combinational map check: internal int_out equals expected
  a_int_out_map: assert property ( int_out == calc_int_out(afl) )
    else $error("flt2int: int_out mapping mismatch");

  // Registered output check: fx_int equals expected function of afl
  a_fx_map: assert property ( fx_int == calc_fx(afl) )
    else $error("flt2int: fx_int mapping mismatch");

  // Split-path checks (redundant with a_fx_map but good triage)
  a_pos_path: assert property ( !afl[31] |-> fx_int == {1'b0, int_out} )
    else $error("flt2int: positive path mismatch");
  a_neg_path: assert property (  afl[31] |-> fx_int == ( {1'b0, ~int_out} + 16'h1 ) )
    else $error("flt2int: negative path mismatch");
  a_pos_msb0: assert property ( !afl[31] |-> fx_int[15] == 1'b0 )
    else $error("flt2int: positive result MSB not zero");

  // Category-specific correctness (concise, high-signal checks)
  a_underflow_zero: assert property ( afl[30:23] < 8'h7f |-> int_out == 15'h0 )
    else $error("flt2int: underflow not zeroed");
  a_exact_7f:       assert property ( afl[30:23] == 8'h7f |-> int_out == 15'h0001 )
    else $error("flt2int: exp=0x7f case incorrect");
  a_overflow_sat:   assert property ( afl[30:23] > 8'h8d |-> int_out == 15'h7fff )
    else $error("flt2int: overflow not saturated");

  // Coverage: exercise all key decode regions and signs
  c_sign_pos:    cover property ( !afl[31] );
  c_sign_neg:    cover property (  afl[31] );

  c_underflow_pos: cover property ( !afl[31] && (afl[30:23] < 8'h7f) );
  c_underflow_neg: cover property (  afl[31] && (afl[30:23] < 8'h7f) );
  c_exp_7f_pos:    cover property ( !afl[31] && (afl[30:23] == 8'h7f) );
  c_exp_7f_neg:    cover property (  afl[31] && (afl[30:23] == 8'h7f) );
  c_overflow_pos:  cover property ( !afl[31] && (afl[30:23] > 8'h8d) );
  c_overflow_neg:  cover property (  afl[31] && (afl[30:23] > 8'h8d) );

  // Cover each explicitly enumerated exponent in 0x80..0x8d
  genvar i;
  generate
    for (i = 0; i <= 13; i++) begin : g_midexp_cov
      localparam logic [7:0] EXP = 8'h80 + i[7:0];
      c_midexp: cover property ( afl[30:23] == EXP );
    end
  endgenerate

endmodule

// Bind to DUT (accessing internal int_out)
bind flt2int flt2int_sva i_flt2int_sva (
  .clk(clk),
  .afl(afl),
  .fx_int(fx_int),
  .int_out(int_out)
);