// SVA checker for mux4. Bind this to the DUT.
module mux4_sva (
  input  logic [3:0] data_in,
  input  logic [1:0] sel,
  input  logic       data_out,
  input  logic       sel_0_bar,
  input  logic       sel_1_bar,
  input  logic       and_1,
  input  logic       and_2,
  input  logic       and_3,
  input  logic       and_4,
  input  logic       or_1,
  input  logic       or_2
);

  // Local decode terms
  logic g1, g2, g3, g4;
  assign g1 = sel_0_bar & sel_1_bar; // 00
  assign g2 = sel_0_bar & sel[1];    // 01
  assign g3 = sel[0]     & sel_1_bar;// 10
  assign g4 = sel[0]     & sel[1];   // 11

  // Inverter checks
  a_inv0: assert property (@(*) sel_0_bar == ~sel[0]);
  a_inv1: assert property (@(*) sel_1_bar == ~sel[1]);

  // Select decode is one-hot
  a_dec_onehot: assert property (@(*) $onehot({g4,g3,g2,g1}));

  // AND stage checks
  a_and1: assert property (@(*) and_1 == (data_in[0] & g1));
  a_and2: assert property (@(*) and_2 == (data_in[1] & g2));
  a_and3: assert property (@(*) and_3 == (data_in[2] & g3));
  a_and4: assert property (@(*) and_4 == (data_in[3] & g4));

  // At most one product term can be 1
  a_and_onehot0: assert property (@(*) $onehot0({and_4,and_3,and_2,and_1}));

  // OR stage checks
  a_or1: assert property (@(*) or_1 == (and_1 | and_2));
  a_or2: assert property (@(*) or_2 == (and_3 | and_4));
  a_out_cone: assert property (@(*) data_out == (or_1 | or_2));

  // End-to-end mux behavior
  a_e2e: assert property (@(*) data_out == data_in[sel]);

  // Functional coverage
  c_sel_00: cover property (@(*) sel == 2'b00);
  c_sel_01: cover property (@(*) sel == 2'b01);
  c_sel_10: cover property (@(*) sel == 2'b10);
  c_sel_11: cover property (@(*) sel == 2'b11);

  c_drive0: cover property (@(*) sel==2'b00 && data_in[0] && data_out);
  c_drive1: cover property (@(*) sel==2'b01 && data_in[1] && data_out);
  c_drive2: cover property (@(*) sel==2'b10 && data_in[2] && data_out);
  c_drive3: cover property (@(*) sel==2'b11 && data_in[3] && data_out);

  c_zero0: cover property (@(*) sel==2'b00 && !data_in[0] && !data_out);
  c_zero1: cover property (@(*) sel==2'b01 && !data_in[1] && !data_out);
  c_zero2: cover property (@(*) sel==2'b10 && !data_in[2] && !data_out);
  c_zero3: cover property (@(*) sel==2'b11 && !data_in[3] && !data_out);

endmodule

bind mux4 mux4_sva chk (.*);