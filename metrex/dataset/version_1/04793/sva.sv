// SVA for binary_adder_tree
// Bind into DUT; checks pipeline, arithmetic width/carry, end-to-end checksum, and key coverage.

module binary_adder_tree_sva (
  input logic              clk,
  input logic [15:0]       A, B, C, D, E, F, G, H, I,
  input logic [15:0]       checksum_reg,
  input logic [16:0]       sum_a_b, sum_c_d, sum_e_f, sum_g_h,
  input logic [16:0]       sum_ab_cd, sum_ef_gh, sum_abcd_efgh, sum_i,
  input logic [16:0]       sumreg_ab, sumreg_cd, sumreg_ef, sumreg_gh,
  input logic [16:0]       sumreg_ab_cd, sumreg_ef_gh, sumreg_abcd_efgh, sumreg_i
);

  default clocking cb @ (posedge clk); endclocking

  // Simple cycle counter for warmup
  logic [7:0] cyc;
  always_ff @(posedge clk) cyc <= cyc + 1'b1;

  // Helper: proper ones-complement fold of 9x16b (A..H at t-5, I at t-1)
  function automatic [15:0] ones_comp_fold9(input logic [15:0] a,b,c,d,e,f,g,h,i);
    logic [19:0] S;
    logic [16:0] t1, t2, t3;
    S  = {4'b0,a}+{4'b0,b}+{4'b0,c}+{4'b0,d}+{4'b0,e}+{4'b0,f}+{4'b0,g}+{4'b0,h}+{4'b0,i};
    t1 = S[15:0] + S[19:16];
    t2 = t1[15:0] + t1[16];
    t3 = t2[15:0] + t2[16];
    ones_comp_fold9 = ~t3[15:0];
  endfunction

  // Combinational adders: ensure carry is preserved correctly (width-accurate)
  // These catch truncation issues (e.g., 16b+16b must reflect a 17b result).
  assert property ({1'b0,A} + {1'b0,B} == sum_a_b);
  assert property ({1'b0,C} + {1'b0,D} == sum_c_d);
  assert property ({1'b0,E} + {1'b0,F} == sum_e_f);
  assert property ({1'b0,G} + {1'b0,H} == sum_g_h);

  assert property (({1'b0,sumreg_ab}     + {1'b0,sumreg_cd})     [16:0] == sum_ab_cd);
  assert property (({1'b0,sumreg_ef}     + {1'b0,sumreg_gh})     [16:0] == sum_ef_gh);
  assert property (({1'b0,sumreg_ab_cd}  + {1'b0,sumreg_ef_gh})  [16:0] == sum_abcd_efgh);
  assert property (({1'b0,sumreg_abcd_efgh}+{1'b0,I})            [16:0] == sum_i);

  // Pipeline register correctness (cycle-accurate)
  assert property (cyc>=1 |-> sumreg_ab        == $past(({1'b0,A}+{1'b0,B})));
  assert property (cyc>=1 |-> sumreg_cd        == $past(({1'b0,C}+{1'b0,D})));
  assert property (cyc>=1 |-> sumreg_ef        == $past(({1'b0,E}+{1'b0,F})));
  assert property (cyc>=1 |-> sumreg_gh        == $past(({1'b0,G}+{1'b0,H})));

  assert property (cyc>=2 |-> sumreg_ab_cd     == $past(( {1'b0,sumreg_ab}    + {1'b0,sumreg_cd}   )[16:0]));
  assert property (cyc>=2 |-> sumreg_ef_gh     == $past(( {1'b0,sumreg_ef}    + {1'b0,sumreg_gh}   )[16:0]));

  assert property (cyc>=3 |-> sumreg_abcd_efgh == $past(( {1'b0,sumreg_ab_cd} + {1'b0,sumreg_ef_gh})[16:0]));

  assert property (cyc>=4 |-> sumreg_i         == $past(( {1'b0,sumreg_abcd_efgh} + {1'b0,I})[16:0]));

  // Final register: end-around-carry then invert (as coded), from previous sumreg_i
  assert property (cyc>=5 |-> checksum_reg == $past( ~(sumreg_i[16] ? (sumreg_i[15:0] + 16'h0001) : sumreg_i[15:0]) ));

  // End-to-end functional check (ones-complement of sum of 9 words, time-aligned to this pipeline)
  assert property (cyc>=6 |-> checksum_reg ==
                   ones_comp_fold9($past(A,5),$past(B,5),$past(C,5),$past(D,5),
                                   $past(E,5),$past(F,5),$past(G,5),$past(H,5),$past(I,1)));

  // X/Z sanitization after warmup at each stage boundary
  assert property (cyc>=1 |-> !$isunknown(sumreg_ab|sumreg_cd|sumreg_ef|sumreg_gh));
  assert property (cyc>=2 |-> !$isunknown(sumreg_ab_cd|sumreg_ef_gh));
  assert property (cyc>=3 |-> !$isunknown(sumreg_abcd_efgh));
  assert property (cyc>=4 |-> !$isunknown(sumreg_i));
  assert property (cyc>=5 |-> !$isunknown(checksum_reg));

  // Key corner-case coverage
  cover property (sum_a_b[16]);                 // carry in A+B
  cover property (sum_c_d[16]);
  cover property (sum_e_f[16]);
  cover property (sum_g_h[16]);
  cover property (sumreg_i[16]);                // final carry before end-around

  cover property (checksum_reg == 16'h0000);
  cover property (checksum_reg == 16'hFFFF);
  cover property (checksum_reg == 16'h1);
endmodule

bind binary_adder_tree binary_adder_tree_sva sva_inst (
  .clk(clk),
  .A(A), .B(B), .C(C), .D(D), .E(E), .F(F), .G(G), .H(H), .I(I),
  .checksum_reg(checksum_reg),
  .sum_a_b(sum_a_b), .sum_c_d(sum_c_d), .sum_e_f(sum_e_f), .sum_g_h(sum_g_h),
  .sum_ab_cd(sum_ab_cd), .sum_ef_gh(sum_ef_gh), .sum_abcd_efgh(sum_abcd_efgh), .sum_i(sum_i),
  .sumreg_ab(sumreg_ab), .sumreg_cd(sumreg_cd), .sumreg_ef(sumreg_ef), .sumreg_gh(sumreg_gh),
  .sumreg_ab_cd(sumreg_ab_cd), .sumreg_ef_gh(sumreg_ef_gh), .sumreg_abcd_efgh(sumreg_abcd_efgh), .sumreg_i(sumreg_i)
);