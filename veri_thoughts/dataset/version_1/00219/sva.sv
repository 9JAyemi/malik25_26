// SVA for RegisterAdd_4: concise, high-quality checks and coverage
module RegisterAdd_4_sva (
  input  logic [3:0] Q_reg,
  input  logic [3:0] D,
  input  logic       CLK,
  input  logic       RST
);

  // Track when $past() is valid
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge CLK) past_valid <= 1'b1;

  // Known/clean signals at clock edge
  ap_known_rst: assert property (@(posedge CLK) !$isunknown(RST))
    else $error("RST is X/Z at posedge CLK");
  ap_known_d:   assert property (@(posedge CLK) !$isunknown(D))
    else $error("D is X/Z at posedge CLK");
  ap_known_q:   assert property (@(posedge CLK) !$isunknown(Q_reg))
    else $error("Q_reg is X/Z at posedge CLK");

  // Synchronous reset drives Q_reg to 0 on that reset edge (checked via $past)
  ap_sync_reset_clears: assert property (@(posedge CLK)
                                         disable iff (!past_valid)
                                         $past(RST) |-> ($past(Q_reg) == 4'h0))
    else $error("Q_reg not 0 on reset cycle");

  // Accumulate when not in reset: Q_reg == (prev Q_reg + prev D) mod 16
  ap_accumulate: assert property (@(posedge CLK)
                                  disable iff (RST || !past_valid)
                                  Q_reg == (($past(Q_reg) + $past(D)) & 4'hF))
    else $error("Q_reg != $past(Q_reg)+$past(D) (mod 16)");

  // No output glitches between clock edges
  ap_no_glitch: assert property (@(negedge CLK) $stable(Q_reg))
    else $error("Q_reg changed outside posedge CLK");

  // Functional coverage
  cv_reset_seen:     cover property (@(posedge CLK) RST);
  cv_reset_release:  cover property (@(posedge CLK) $fell(RST));
  cv_add_zero:       cover property (@(posedge CLK)
                                     disable iff (RST || !past_valid)
                                     ($past(D) == 4'h0));
  cv_add_max:        cover property (@(posedge CLK)
                                     disable iff (RST || !past_valid)
                                     ($past(D) == 4'hF));
  cv_add_no_wrap:    cover property (@(posedge CLK)
                                     disable iff (RST || !past_valid)
                                     (($past(Q_reg) + $past(D)) < 16));
  cv_add_wrap:       cover property (@(posedge CLK)
                                     disable iff (RST || !past_valid)
                                     (($past(Q_reg) + $past(D)) >= 16));
endmodule

bind RegisterAdd_4 RegisterAdd_4_sva sva_inst (.Q_reg(Q_reg), .D(D), .CLK(CLK), .RST(RST));