// SVA for bridge. Bind this file to the DUT.
// Notes:
// - The case decode in RTL uses {OPT,KEY} (10b) with 8b literals; we mirror the actual behavior (8b zero-extended to 10b).
// - 8'b00000010 appears twice in RTL; only the first branch can take effect. zero_reg is effectively stuck at 0 after reset.

bind bridge bridge_sva b_bridge_sva();

module bridge_sva;
  // Local mirror of the RTL decode
  localparam [9:0] ENC_SRL1 = 10'b00_00000000; // shift right 1
  localparam [9:0] ENC_SRR2 = 10'b00_00000001; // shift right 2
  localparam [9:0] ENC_SLL1 = 10'b00_00000010; // shift left 1
  localparam [9:0] ENC_SLL2 = 10'b00_00000011; // shift left 2
  localparam [9:0] ENC_NOT  = 10'b00_00000100; // bitwise not

  wire [9:0] sel = {OPT, KEY};

  default clocking cb @(posedge CLK); endclocking
  default disable iff (!RST);

  // Reset behavior
  assert property (@(posedge CLK or negedge RST) !RST |-> (shift_reg==8'h00 && not_reg==8'h00 && zero_reg==8'h00));

  // Enable gating: hold when ENA==0
  assert property (!ENA |=> $stable({shift_reg, not_reg, zero_reg}));

  // Exact functional updates on ENA with each decode
  assert property (ENA && (sel==ENC_SLL1) |=> shift_reg=={RGA[6:0],1'b0} && $stable(not_reg) && $stable(zero_reg));
  assert property (ENA && (sel==ENC_SRL1) |=> shift_reg=={1'b0, RGA[7:1]} && $stable(not_reg) && $stable(zero_reg));
  assert property (ENA && (sel==ENC_SLL2) |=> shift_reg=={RGA[5:0],2'b00} && $stable(not_reg) && $stable(zero_reg));
  assert property (ENA && (sel==ENC_SRR2) |=> shift_reg=={2'b00, RGA[7:2]} && $stable(not_reg) && $stable(zero_reg));
  assert property (ENA && (sel==ENC_NOT)  |=> not_reg==~RGA && $stable(shift_reg) && $stable(zero_reg));

  // Default case when none of the above encodings match
  assert property (ENA && !(sel inside {ENC_SLL1,ENC_SRL1,ENC_SLL2,ENC_SRR2,ENC_NOT})
                   |=> shift_reg==RGA && $stable(not_reg) && $stable(zero_reg));

  // zero_reg is effectively constant zero after reset
  assert property (zero_reg==8'h00);

  // At most one internal register changes per enabled cycle
  assert property (ENA |-> $onehot0({shift_reg!=$past(shift_reg),
                                     not_reg  !=$past(not_reg),
                                     zero_reg !=$past(zero_reg)}));

  // Output mux correctness
  assert property (RGZ == (RGB ? not_reg : ((KEY==2'b10) ? zero_reg : shift_reg)));

  // No X on output when out of reset
  assert property (!$isunknown(RGZ)));

  // --------------------
  // Functional coverage
  // --------------------
  cover property ($fell(RST));
  cover property ($rose(RST));

  cover property (ENA && (sel==ENC_SLL1));
  cover property (ENA && (sel==ENC_SRL1));
  cover property (ENA && (sel==ENC_SLL2));
  cover property (ENA && (sel==ENC_SRR2));
  cover property (ENA && (sel==ENC_NOT));
  cover property (ENA && !(sel inside {ENC_SLL1,ENC_SRL1,ENC_SLL2,ENC_SRR2,ENC_NOT}));

  cover property (RGB);                 // RGZ selects not_reg
  cover property (!RGB && KEY==2'b10);  // RGZ selects zero_reg
  cover property (!RGB && KEY!=2'b10);  // RGZ selects shift_reg
endmodule