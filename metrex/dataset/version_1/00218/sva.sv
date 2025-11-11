// SVA for top_module, decoder_2to4_with_enable, and booth_multiplier
// Focused, bind-ready, with key checks and concise coverage

// ---------- top-level checks ----------
module top_module_sva (
  input logic               clk,
  input logic               reset,
  input logic               EN,
  input  signed logic [7:0] multiplier_out,
  input  signed logic [7:0] P_output,
  input  signed logic [3:0] A,
  input  signed logic [3:0] B
);
  default clocking cb @(posedge clk); endclocking

  // Async reset observable at clk edge
  ap_top_reset:       assert property (reset |-> P_output == 8'sd0);
  // Gating behavior
  ap_top_gate:        assert property (disable iff (reset) P_output == $past(EN ? multiplier_out : 8'sd0));
  // Known outputs
  ap_top_known:       assert property (disable iff (reset) !$isunknown(P_output));

  // Concise coverage
  cp_en_0_1:          cover property (disable iff (reset) !EN ##1 EN ##1 !EN);
  cp_p_nonzero:       cover property (disable iff (reset) EN ##1 P_output != 8'sd0);
  cp_A_min:           cover property (A == -8);
  cp_A_max:           cover property (A ==  7);
  cp_B_min:           cover property (B == -8);
  cp_B_max:           cover property (B ==  7);
endmodule

// ---------- decoder checks ----------
module decoder_2to4_with_enable_sva (
  input logic clk,
  input logic A,
  input logic B,
  input logic EN,
  input logic [3:0] Y
);
  default clocking cb @(posedge clk); endclocking

  // Legal code words (onehot0)
  ap_dec_onehot0:     assert property ($onehot0(Y));
  ap_dec_known:       assert property (!$isunknown(Y));

  // Implemented truth table (matches DUT case)
  ap_dec_A1_zero:     assert property (A               |-> Y == 4'b0000);
  ap_dec_000:         assert property (!A && !B && !EN |-> Y == 4'b0001);
  ap_dec_001:         assert property (!A && !B &&  EN |-> Y == 4'b0010);
  ap_dec_010:         assert property (!A &&  B && !EN |-> Y == 4'b0100);
  ap_dec_011:         assert property (!A &&  B &&  EN |-> Y == 4'b1000);

  // Coverage of all outputs
  cp_Y_0000:          cover property (A && Y == 4'b0000);
  cp_Y_0001:          cover property (!A && !B && !EN && Y == 4'b0001);
  cp_Y_0010:          cover property (!A && !B &&  EN && Y == 4'b0010);
  cp_Y_0100:          cover property (!A &&  B && !EN && Y == 4'b0100);
  cp_Y_1000:          cover property (!A &&  B &&  EN && Y == 4'b1000);
endmodule

// ---------- booth multiplier checks ----------
module booth_multiplier_sva (
  input  logic               clk,
  input  logic               reset,
  input  signed logic  [3:0] A,
  input  signed logic  [3:0] B,
  input  signed logic  [7:0] P,
  input  signed logic  [7:0] P_reg,
  input  signed logic  [3:0] A_reg,
  input  signed logic  [3:0] B_reg,
  input  logic        [2:0]  state
);
  default clocking cb @(posedge clk); endclocking

  // Reset values
  ap_bm_reset:        assert property (reset |-> (P_reg == 8'sd0 && A_reg == 4'sd0 && B_reg == 4'sd0 && state == 3'b000));
  // P mirrors P_reg (combinational drive)
  ap_bm_P_eq_Preg:    assert property (!$isunknown(P) && P == P_reg);
  // State legality
  ap_bm_state_legal:  assert property (disable iff (reset) state inside {3'b000,3'b001,3'b010,3'b011});

  // State 000 -> 001 with loads and initial partial product
  ap_s000: assert property (disable iff (reset)
    state == 3'b000 |=> (state == 3'b001) &&
                        (A_reg == $past(A)) &&
                        (B_reg == $past(B)) &&
                        (P_reg == ($past(B[0]) ? -$past(A) : $past(A)))
  );

  // State 001 -> 010 with shift and conditional +/- 2*A_reg based on B[1:0]
  ap_s001: assert property (disable iff (reset)
    state == 3'b001 |=> (state == 3'b010) &&
                        (A_reg == ($past(A_reg) << 1)) &&
                        (B_reg == ($past(B) >> 1)) &&
                        (P_reg ==
                          (($past(B[0]) && !$past(B[1])) ? ($past(P_reg) - ($past(A_reg) << 1)) :
                           ((!$past(B[0]) && $past(B[1])) ? ($past(P_reg) + ($past(A_reg) << 1)) :
                                                            $past(P_reg)))
                        )
  );

  // State 010 -> 011 with +/- B_reg based on B[0], shift B_reg
  ap_s010: assert property (disable iff (reset)
    state == 3'b010 |=> (state == 3'b011) &&
                        (A_reg == $past(A_reg)) &&
                        (B_reg == ($past(B_reg) >> 1)) &&
                        (P_reg == ($past(B[0]) ? ($past(P_reg) - $past(B_reg))
                                               : ($past(P_reg) + $past(B_reg))))
  );

  // State 011 -> 000, hold regs
  ap_s011: assert property (disable iff (reset)
    state == 3'b011 |=> (state == 3'b000) &&
                        (A_reg == $past(A_reg)) &&
                        (B_reg == $past(B_reg)) &&
                        (P_reg == $past(P_reg))
  );

  // Coverage: one full FSM cycle and both arithmetic branches
  cp_cycle:            cover property (disable iff (reset)
                        state==3'b000 ##1 state==3'b001 ##1 state==3'b010 ##1 state==3'b011 ##1 state==3'b000);
  cp_s001_sub:         cover property (disable iff (reset) state==3'b001 &&  B[0] && !B[1]);
  cp_s001_add:         cover property (disable iff (reset) state==3'b001 && !B[0] &&  B[1]);
  cp_s010_sub:         cover property (disable iff (reset) state==3'b010 &&  B[0]);
  cp_s010_add:         cover property (disable iff (reset) state==3'b010 && !B[0]);
  cp_P_nonzero:        cover property (disable iff (reset) P != 8'sd0);
endmodule

// ---------- binds ----------
bind top_module                             top_module_sva             u_top_sva (.*);
bind top_module.decoder_2to4_with_enable_inst
                                            decoder_2to4_with_enable_sva u_dec_sva (.clk(clk), .A(A_input), .B(B_input), .EN(EN), .Y(decoder_out));
bind booth_multiplier                       booth_multiplier_sva       u_bm_sva (.clk(clk), .reset(reset), .A(A), .B(B), .P(P), .P_reg(P_reg), .A_reg(A_reg), .B_reg(B_reg), .state(state));