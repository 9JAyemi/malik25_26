// SVA for led_controller. Bind this to the DUT.
// Concise, full functional checks and coverage.

module led_controller_sva (led_controller dut);

  // Vector aliases for brevity
  wire [3:0] sw  = {dut.SW_3,  dut.SW_2,  dut.SW_1,  dut.SW_0};
  wire [3:0] led = {dut.LED_3, dut.LED_2, dut.LED_1, dut.LED_0};

  // Core functional relation: outputs are bitwise inversion of inputs (when inputs known)
  a_inv_vec: assert property (@(sw or led) (!$isunknown(sw)) |-> (led === ~sw));

  // Outputs should never go X/Z
  a_no_xz_out: assert property (@(sw or led) !$isunknown(led));

  // Outputs equal internal state registers (structural consistency)
  a_out_eq_state: assert property (@(led)
    (dut.LED_0 === dut.LED_0_state) &&
    (dut.LED_1 === dut.LED_1_state) &&
    (dut.LED_2 === dut.LED_2_state) &&
    (dut.LED_3 === dut.LED_3_state)
  );

  // Per-bit immediate inversion on edges and no spurious output changes
  genvar i;
  generate
    for (i=0; i<4; i++) begin : per_bit
      a_edge_rise: assert property (@(sw[i] or led[i]) $rose(sw[i]) |-> ##0 $fell(led[i]));
      a_edge_fall: assert property (@(sw[i] or led[i]) $fell(sw[i]) |-> ##0 $rose(led[i]));
      a_no_spurious: assert property (@(sw[i] or led[i]) $changed(led[i]) |-> $changed(sw[i]));

      // Per-bit toggle coverage (both directions)
      c_sw_rise: cover property (@(sw[i]) $rose(sw[i]) ##0 $fell(led[i]));
      c_sw_fall: cover property (@(sw[i]) $fell(sw[i]) ##0 $rose(led[i]));
    end
  endgenerate

  // Full functional coverage of all 16 input combinations with correct outputs
  genvar v;
  generate
    for (v=0; v<16; v++) begin : cov_all
      localparam logic [3:0] VAL = v[3:0];
      c_all_vals: cover property (@(sw or led) (sw == VAL) && (led == ~VAL));
    end
  endgenerate

endmodule

// Bind into every led_controller instance
bind led_controller led_controller_sva u_led_controller_sva (.dut());