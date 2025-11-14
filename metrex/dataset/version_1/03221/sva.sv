// SVA checker for ACA_I_N32_Q8
// Bind this module to the DUT; focuses on correctness of temps and res mapping.
// Concise, full coverage of key behaviors.

module ACA_I_N32_Q8_sva (
  input  logic [31:0] in1,
  input  logic [31:0] in2,
  input  logic [32:0] res,
  input  logic [8:0]  temp1, temp2, temp3, temp4, temp5,
  input  logic [8:0]  temp6, temp7, temp8, temp9, temp10,
  input  logic [8:0]  temp11, temp12, temp13, temp14, temp15,
  input  logic [8:0]  temp16, temp17, temp18, temp19, temp20,
  input  logic [8:0]  temp21, temp22, temp23, temp24, temp25
);

  function automatic [8:0] sum8(input logic [7:0] a, input logic [7:0] b);
    sum8 = a + b;
  endfunction

  // No X/Z on primary IOs and temps
  assert property (@(in1 or in2 or res)
                   !$isunknown({in1,in2,res,
                                temp1,temp2,temp3,temp4,temp5,temp6,temp7,temp8,temp9,temp10,
                                temp11,temp12,temp13,temp14,temp15,temp16,temp17,temp18,temp19,temp20,
                                temp21,temp22,temp23,temp24,temp25}));

  // Check each tempN = zero-extended sum of corresponding 8-bit window
  `define CHK_TEMP(N) \
    assert property (@(in1 or in2) 1 |-> ##0 \
      (temp``N == sum8( in1[(N+6) -: 8], in2[(N+6) -: 8] )))
  `CHK_TEMP(1);
  `CHK_TEMP(2);
  `CHK_TEMP(3);
  `CHK_TEMP(4);
  `CHK_TEMP(5);
  `CHK_TEMP(6);
  `CHK_TEMP(7);
  `CHK_TEMP(8);
  `CHK_TEMP(9);
  `CHK_TEMP(10);
  `CHK_TEMP(11);
  `CHK_TEMP(12);
  `CHK_TEMP(13);
  `CHK_TEMP(14);
  `CHK_TEMP(15);
  `CHK_TEMP(16);
  `CHK_TEMP(17);
  `CHK_TEMP(18);
  `CHK_TEMP(19);
  `CHK_TEMP(20);
  `CHK_TEMP(21);
  `CHK_TEMP(22);
  `CHK_TEMP(23);
  `CHK_TEMP(24);
  `CHK_TEMP(25);
  `undef CHK_TEMP

  // Output mapping checks
  // LSB byte equals low 8 bits of sum over [7:0]
  assert property (@(in1 or in2) 1 |-> ##0
    (res[7:0] == sum8(in1[7:0], in2[7:0])[7:0]));

  // Bits 8..31 equal bit[7] of sliding 8-bit window sums; bit 32 equals carry of top window
  genvar k;
  generate
    for (k = 8; k <= 31; k++) begin : g_mid_bits
      assert property (@(in1 or in2) 1 |-> ##0
        (res[k] == sum8( in1[k -: 8], in2[k -: 8] )[7]));
    end
  endgenerate
  assert property (@(in1 or in2) 1 |-> ##0
    (res[32] == sum8(in1[31 -: 8], in2[31 -: 8])[8]));

  // Coverage: extremes, dropped LSB carry, window MSB activity, top carry
  cover property (@(in1 or in2) (in1 == 32'd0 && in2 == 32'd0));
  cover property (@(in1 or in2) (in1 == 32'hFFFF_FFFF && in2 == 32'hFFFF_FFFF));
  cover property (@(in1 or in2) sum8(in1[7:0],  in2[7:0])[8]);    // dropped carry from LSB window
  cover property (@(in1 or in2) res[32]);                         // top carry observed
  generate
    for (k = 8; k <= 31; k++) begin : g_msb_covers
      cover property (@(in1 or in2) sum8(in1[k -: 8], in2[k -: 8])[7]);
    end
  endgenerate

endmodule

// Bind into the DUT
bind ACA_I_N32_Q8 ACA_I_N32_Q8_sva i_ACA_I_N32_Q8_sva (.*);