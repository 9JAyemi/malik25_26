// SVA for clock_gate
module clock_gate_sva #(parameter WIDTH=32) (
  input CLK, EN, TE,
  input [WIDTH-1:0] W,
  input ENCLK,
  input [WIDTH-1:0] Y
);

  default clocking cb @(posedge CLK); endclocking

  // ENCLK function: sampled after NBA at this posedge
  a_enclk_val:                 assert property (##0 ENCLK == (TE || EN));

  // ENCLK edges and their causes
  a_enclk_rise_cause:          assert property (##0 $rose(ENCLK) |-> (TE || EN));
  a_enclk_fall_cause:          assert property (##0 $fell(ENCLK) |-> !(TE || EN));

  // ENCLK edges only align with CLK posedge (no glitches)
  a_enclk_rises_only_at_clk:   assert property (@(posedge ENCLK) $rose(CLK));
  a_enclk_falls_only_at_clk:   assert property (@(negedge ENCLK) $rose(CLK));

  // Y updates exactly on ENCLK rising edge and captures W
  a_y_capture_on_enclk:        assert property (@(posedge ENCLK) ##0 Y == W);

  // Y cannot change without an ENCLK rising edge
  a_y_changes_only_on_enclk:   assert property (##0 $changed(Y) |-> $rose(ENCLK));

  // Coverage
  c_en_path:    cover property (@(posedge ENCLK) EN && !TE);
  c_te_path:    cover property (@(posedge ENCLK) TE && !EN);
  c_gate_off:   cover property (@(posedge CLK) !TE && !EN ##0 !ENCLK);
  c_enclk_fall: cover property (@(posedge CLK) ##0 $fell(ENCLK));
  c_y_cap:      cover property (@(posedge ENCLK) ##0 Y == W);

endmodule

bind clock_gate clock_gate_sva #(.WIDTH(32)) u_clock_gate_sva (.*);