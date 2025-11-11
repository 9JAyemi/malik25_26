// SVA checker for ripple_carry_adder (bindable, concise, high-quality)
// Assumes a free-running clk; sample on posedge.
module ripple_carry_adder_sva (
  input  logic        clk,
  // DUT ports
  input  logic [7:0]  in1,
  input  logic [7:0]  in2,
  input  logic [8:0]  res,
  // DUT internal nets we want to check
  input  logic        p0,p1,p2,p3,p4,p5,p6,
  input  logic        g0,g1,g2,g3,g4,g5,g6,
  input  logic        c1,c2,c3,c4,c5,c6,c7,
  input  logic        carry_pred_1,carry_pred_2,carry_pred_3,
                      carry_pred_4,carry_pred_5,carry_pred_6
);
  default clocking cb @ (posedge clk); endclocking

  // Reference p/g and canonical carry chain (true ripple/CLA from c0=0)
  logic [7:0] p_ref, g_ref;
  logic [7:0] c_out_ref; // carry-out after bit i (i=0..7)
  logic [8:0] res_ref;

  assign p_ref = in1 ^ in2;
  assign g_ref = in1 & in2;

  // carry-out after bit0..bit7
  always_comb begin
    c_out_ref[0] = g_ref[0];
    for (int i = 1; i < 8; i++) begin
      c_out_ref[i] = g_ref[i] | (p_ref[i] & c_out_ref[i-1]);
    end
    // expected sum/result
    res_ref[0] = p_ref[0];
    for (int i = 1; i < 8; i++) begin
      res_ref[i] = p_ref[i] ^ c_out_ref[i-1];
    end
    res_ref[8] = c_out_ref[7];
  end

  // Basic sanity: no X/Z on key I/O
  assert property (!$isunknown({in1,in2,res})));

  // p/g correctness (bits 0..6)
  assert property ({p6,p5,p4,p3,p2,p1,p0} == p_ref[6:0]);
  assert property ({g6,g5,g4,g3,g2,g1,g0} == g_ref[6:0]);

  // c1 must be carry-out of bit0
  assert property (c1 == c_out_ref[0]);

  // Predicted carries must equal true canonical carries
  assert property ({carry_pred_6,carry_pred_5,carry_pred_4,
                    carry_pred_3,carry_pred_2,carry_pred_1} == c_out_ref[6:1]);

  // Bit-level sum and final carry-out
  assert property (res == res_ref);

  // End-to-end arithmetic equivalence
  assert property (res == in1 + in2);

  // Minimal but meaningful coverage
  cover property (res == in1 + in2);     // functional hit
  cover property (res[8]);               // overflow occurs
  cover property (&p_ref[6:1] && g_ref[0]); // long propagate chain from bit0 through bit6
  cover property (carry_pred_1);
  cover property (carry_pred_2);
  cover property (carry_pred_3);
  cover property (carry_pred_4);
  cover property (carry_pred_5);
  cover property (carry_pred_6);
endmodule

// Example bind (connect clk from your TB):
// bind ripple_carry_adder ripple_carry_adder_sva u_rca_sva (
//   .clk(tb_clk),
//   .in1(in1), .in2(in2), .res(res),
//   .p0(p0), .p1(p1), .p2(p2), .p3(p3), .p4(p4), .p5(p5), .p6(p6),
//   .g0(g0), .g1(g1), .g2(g2), .g3(g3), .g4(g4), .g5(g5), .g6(g6),
//   .c1(c1), .c2(c2), .c3(c3), .c4(c4), .c5(c5), .c6(c6), .c7(c7),
//   .carry_pred_1(carry_pred_1), .carry_pred_2(carry_pred_2), .carry_pred_3(carry_pred_3),
//   .carry_pred_4(carry_pred_4), .carry_pred_5(carry_pred_5), .carry_pred_6(carry_pred_6)
// );