// SVA for sky130_fd_sc_hd__fa
// Bind this module into the DUT and drive clk/rst_n from your env.
module sky130_fd_sc_hd__fa_sva (input logic clk, rst_n);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Functional correctness (full-adder)
  assert property ({COUT,SUM} === (A + B + CIN));
  assert property (SUM  === (A ^ B ^ CIN));
  assert property (COUT === ((A & B) | (A & CIN) | (B & CIN)));

  // Combinational purity: outputs don’t change if inputs don’t
  assert property ($stable({A,B,CIN}) |-> $stable({COUT,SUM}));

  // Internal net-level correctness (checks gate wiring)
  assert property (or0_out      === (CIN | B));
  assert property (and0_out     === (or0_out & A));
  assert property (and1_out     === (B & CIN));
  assert property (or1_out_COUT === (and1_out | and0_out));
  assert property (COUT         === or1_out_COUT);

  assert property (and2_out     === (CIN & A & B));
  assert property (nor0_out     === ~(A | or0_out));
  assert property (nor1_out     === ~(nor0_out | COUT));
  assert property (or2_out_SUM  === (nor1_out | and2_out));
  assert property (SUM          === or2_out_SUM);

  // Power/ground rails integrity
  assert property (VPWR === 1'b1);
  assert property (VPB  === 1'b1);
  assert property (VGND === 1'b0);
  assert property (VNB  === 1'b0);

  // Functional coverage: all 8 input combinations and expected outputs
  cover property (A==0 && B==0 && CIN==0 && {COUT,SUM}==2'b00);
  cover property (A==0 && B==0 && CIN==1 && {COUT,SUM}==2'b01);
  cover property (A==0 && B==1 && CIN==0 && {COUT,SUM}==2'b01);
  cover property (A==0 && B==1 && CIN==1 && {COUT,SUM}==2'b10);
  cover property (A==1 && B==0 && CIN==0 && {COUT,SUM}==2'b01);
  cover property (A==1 && B==0 && CIN==1 && {COUT,SUM}==2'b10);
  cover property (A==1 && B==1 && CIN==0 && {COUT,SUM}==2'b10);
  cover property (A==1 && B==1 && CIN==1 && {COUT,SUM}==2'b11);
endmodule

// Example bind (provide clk/rst_n from your environment):
// bind sky130_fd_sc_hd__fa sky130_fd_sc_hd__fa_sva fa_sva_i (.clk(clk), .rst_n(rst_n));