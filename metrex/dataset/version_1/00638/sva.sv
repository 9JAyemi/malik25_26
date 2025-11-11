// SVA for user_design
module user_design_sva (
  input logic ETH_CLK_OBUF,
  input logic INTERNAL_RST_reg,
  input logic OUT1_STB,
  input logic IN1_ACK,
  input logic [7:0] OUT1,
  input logic IN1_STB,
  input logic OUT1_ACK,
  input logic [7:0] output_rs232_tx
);

  default clocking cb @(posedge ETH_CLK_OBUF); endclocking

  // No X on outputs
  a_no_x_outputs: assert property (! $isunknown({IN1_STB, OUT1_ACK, output_rs232_tx}));

  // Data path: pure combinational pass-through
  a_tx_passthrough: assert property (output_rs232_tx == OUT1);

  // STB mapping with reset override
  a_stb_map:        assert property (IN1_STB == (INTERNAL_RST_reg ? 1'b0 : OUT1_STB));

  // Reset forces outputs low
  a_rst_ack_low:    assert property (INTERNAL_RST_reg |-> (OUT1_ACK == 1'b0));
  a_rst_stb_low:    assert property (INTERNAL_RST_reg |-> (IN1_STB  == 1'b0));

  // ACK behavior
  // When IN1_ACK and not in reset, OUT1_ACK must assert same cycle
  a_ack_assert_on_in1ack: assert property ((!INTERNAL_RST_reg && IN1_ACK) |-> OUT1_ACK);

  // OUT1_ACK can change only due to IN1_ACK or reset
  a_ack_changes_only_on_events: assert property ($changed(OUT1_ACK) |-> (INTERNAL_RST_reg || IN1_ACK));

  // 0->1 only when IN1_ACK; 1->0 only with reset
  a_ack_rise_cause: assert property ((!INTERNAL_RST_reg && $rose(OUT1_ACK)) |-> IN1_ACK);
  a_ack_fall_only_reset: assert property ($fell(OUT1_ACK) |-> INTERNAL_RST_reg);

  // Sticky high until reset (step-wise hold)
  a_ack_sticky_until_reset: assert property (disable iff (INTERNAL_RST_reg) OUT1_ACK |=> OUT1_ACK);

  // Output constraints when IN1_STB is high (sanity)
  a_stb_implies_inputs: assert property (IN1_STB |-> (!INTERNAL_RST_reg && OUT1_STB));

  // Coverage
  c_reset_seq:     cover property (INTERNAL_RST_reg ##1 !INTERNAL_RST_reg);
  c_ack_set_hold:  cover property (!INTERNAL_RST_reg && IN1_ACK ##1 OUT1_ACK ##[1:$] INTERNAL_RST_reg);
  c_stb_mirror:    cover property (!INTERNAL_RST_reg && $changed(OUT1_STB) && (IN1_STB == OUT1_STB));
  c_data_change:   cover property ($changed(OUT1) && (output_rs232_tx == OUT1));

endmodule

bind user_design user_design_sva u_user_design_sva (.*);