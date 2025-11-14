// SVA checker for siete_segmentos_principal
// Bind this to your DUT and connect a clock/reset from your environment.
module siete_segmentos_principal_sva (
  input logic clk,
  input logic rst_n,

  input  logic bitA, bitB, bitC, bitD,
  input  logic en1, en2, en3, en4,
  input  logic seg_a, seg_b, seg_c, seg_d, seg_e, seg_f, seg_g,
  input  logic s_seg1, s_seg2, s_seg3, s_seg4
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Expected combinational functions (mirrors DUT)
  logic exp_s_seg1, exp_s_seg2, exp_s_seg3, exp_s_seg4;
  assign exp_s_seg1 = !en1;
  assign exp_s_seg2 = !en2;
  assign exp_s_seg3 = !en3;
  assign exp_s_seg4 = !en4;

  logic exp_seg_a, exp_seg_b, exp_seg_c, exp_seg_d, exp_seg_e, exp_seg_f, exp_seg_g;
  assign exp_seg_a = !((!bitB&!bitD)|(!bitA&bitC)|(!bitA&bitB&bitD)|(bitB&bitC)|(bitA&!bitD)|(bitA&!bitB&!bitC));
  assign exp_seg_b = !((bitA&!bitC&bitD)|(!bitB&!bitD)|(!bitA&!bitC&!bitD)|(!bitA&bitC&bitD)|(!bitA&!bitB));
  assign exp_seg_c = !((!bitC&bitD)|(!bitA&bitB)|(bitA&!bitB)|(!bitA&!bitC)|(!bitA&bitD));
  assign exp_seg_d = !((bitB&!bitC&bitD)|(!bitB&bitC&bitD)|(bitB&bitC&!bitD)|(bitA&!bitC)|(!bitA&!bitB&!bitD));
  assign exp_seg_e = !((!bitB&!bitD)|(bitC&!bitD)|(bitA&bitC)|(bitA&bitB));
  assign exp_seg_f = !((!bitC&!bitD)|(bitB&!bitD)|(!bitA&bitB&!bitC)|(bitA&!bitB)|(bitA&bitC));
  assign exp_seg_g = !((!bitB&bitC)|(bitA&!bitB)|(bitA&bitD)|(bitC&!bitD)|(!bitA&bitB&!bitC));

  // Sanity: no X/Z on inputs and outputs
  ap_inputs_known:  assert property (!$isunknown({bitA,bitB,bitC,bitD,en1,en2,en3,en4}));
  ap_outputs_known: assert property (!$isunknown({seg_a,seg_b,seg_c,seg_d,seg_e,seg_f,seg_g,s_seg1,s_seg2,s_seg3,s_seg4}));

  // Functional equivalence checks (golden = RTL equations)
  ap_sseg1: assert property (s_seg1 == exp_s_seg1);
  ap_sseg2: assert property (s_seg2 == exp_s_seg2);
  ap_sseg3: assert property (s_seg3 == exp_s_seg3);
  ap_sseg4: assert property (s_seg4 == exp_s_seg4);

  ap_seg_a: assert property (seg_a == exp_seg_a);
  ap_seg_b: assert property (seg_b == exp_seg_b);
  ap_seg_c: assert property (seg_c == exp_seg_c);
  ap_seg_d: assert property (seg_d == exp_seg_d);
  ap_seg_e: assert property (seg_e == exp_seg_e);
  ap_seg_f: assert property (seg_f == exp_seg_f);
  ap_seg_g: assert property (seg_g == exp_seg_g);

  // Independence checks (decoupling of buses)
  ap_seg_indep_of_en:  assert property ($stable({bitA,bitB,bitC,bitD}) |-> ##1 $stable({seg_a,seg_b,seg_c,seg_d,seg_e,seg_f,seg_g}));
  ap_sseg_indep_of_bits: assert property ($stable({en1,en2,en3,en4}) |-> ##1 $stable({s_seg1,s_seg2,s_seg3,s_seg4}));

  // Combinational stability: if all inputs hold, outputs hold next cycle (no cycle-to-cycle glitch)
  ap_hold_when_inputs_hold: assert property ($stable({bitA,bitB,bitC,bitD,en1,en2,en3,en4}) |-> ##1 $stable({seg_a,seg_b,seg_c,seg_d,seg_e,seg_f,seg_g,s_seg1,s_seg2,s_seg3,s_seg4}));

  // Coverage: exercise all 16 data codes
  genvar gi;
  generate
    for (gi=0; gi<16; gi++) begin : CODES
      cover property ({bitA,bitB,bitC,bitD} == gi[3:0]);
    end
  endgenerate

  // Coverage: exercise all 16 enable combinations
  genvar ge;
  generate
    for (ge=0; ge<16; ge++) begin : ENS
      cover property ({en1,en2,en3,en4} == ge[3:0]);
    end
  endgenerate

  // Coverage: each output toggles both ways at least once
  `define TOG_COV(sig) \
    cover property ($rose(sig)); \
    cover property ($fell(sig));

  `TOG_COV(seg_a)
  `TOG_COV(seg_b)
  `TOG_COV(seg_c)
  `TOG_COV(seg_d)
  `TOG_COV(seg_e)
  `TOG_COV(seg_f)
  `TOG_COV(seg_g)
  `TOG_COV(s_seg1)
  `TOG_COV(s_seg2)
  `TOG_COV(s_seg3)
  `TOG_COV(s_seg4)

  `undef TOG_COV

endmodule

// Example bind (edit clk/rst_n to match your environment):
// bind siete_segmentos_principal siete_segmentos_principal_sva u_sva (
//   .clk(tb_clk), .rst_n(tb_rst_n),
//   .bitA(bitA), .bitB(bitB), .bitC(bitC), .bitD(bitD),
//   .en1(en1), .en2(en2), .en3(en3), .en4(en4),
//   .seg_a(seg_a), .seg_b(seg_b), .seg_c(seg_c), .seg_d(seg_d), .seg_e(seg_e), .seg_f(seg_f), .seg_g(seg_g),
//   .s_seg1(s_seg1), .s_seg2(s_seg2), .s_seg3(s_seg3), .s_seg4(s_seg4)
// );