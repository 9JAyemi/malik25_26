Below is a concise SVA bind set that checks functional correctness, no-X/Z cleanliness, and key corner-case coverage for both modules.

module t_sva (
  input clk,
  input        ina_w1,
  input [60:0] inb_w61,
  input [29:0] outc_w30,
  input [72:0] outd_w73
);
  default clocking cb @(posedge clk); endclocking

  // Cleanliness
  ap_inputs_clean:  assert (!$isunknown({ina_w1,inb_w61}));
  ap_outputs_clean: assert (!$isunknown({outc_w30,outd_w73}));

  // Functional correctness
  // Subtraction: check lower 30 bits of 31-bit result {30'b0,ina} - inb[30:0]
  ap_sub_ok: assert (outc_w30 === ({30'b0, ina_w1} - inb_w61[30:0])[29:0]);

  // Multiplication: direct functional check
  ap_mul_ok: assert (outd_w73 === (ina_w1 * inb_w61));

  // Structural width checks for multiply (1b * 61b => 62b => zero-extended to 73b)
  ap_mul_upper_zero: assert (outd_w73[72:61] == 12'd0);
  ap_mul_by_0:       assert (ina_w1==1'b0 |-> outd_w73 == 73'd0);
  ap_mul_by_1:       assert (ina_w1==1'b1 |-> outd_w73 == {12'd0, inb_w61});

  // Coverage
  cp_ina0:        cover (ina_w1==1'b0);
  cp_ina1:        cover (ina_w1==1'b1);
  cp_inb_zero:    cover (inb_w61=='0);
  cp_inb_allones: cover (&inb_w61);
  cp_sub_borrow:  cover (({30'b0, ina_w1} - inb_w61[30:0])[30]);     // borrow occurred
  cp_sub_noborr:  cover (!({30'b0, ina_w1} - inb_w61[30:0])[30]);    // no borrow
  cp_mul_nonzero: cover (ina_w1 && |inb_w61);
endmodule


module sub_sva (
  input clk,
  input        inw_w31,
  input [60:0] inx_w11,
  input [91:0] outy_w92,
  input [21:0] outz_w22,
  input [29:0] outc_w30,
  input [72:0] outd_w73
);
  default clocking cb @(posedge clk); endclocking

  // Cleanliness (will flag undriven outputs/wires)
  ap_sub_in_clean:   assert (!$isunknown({inw_w31,inx_w11}));
  ap_sub_out_clean:  assert (!$isunknown({outy_w92,outz_w22}));
  ap_sub_int_clean:  assert (!$isunknown({outc_w30,outd_w73}));

  // Basic liveness coverage (catch stuck-at)
  cp_outy_tog: cover ($changed(outy_w92));
  cp_outz_tog: cover ($changed(outz_w22));
endmodule


bind t   t_sva  t_sva_b  (.clk(clk), .ina_w1(ina_w1), .inb_w61(inb_w61), .outc_w30(outc_w30), .outd_w73(outd_w73));
bind sub sub_sva sub_sva_b(.clk(clk), .inw_w31(inw_w31), .inx_w11(inx_w11), .outy_w92(outy_w92), .outz_w22(outz_w22), .outc_w30(outc_w30), .outd_w73(outd_w73));