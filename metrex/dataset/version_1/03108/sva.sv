// SVA for fsm_module
module fsm_module_sva
(
  input logic        div_clock,
  input logic        reset,
  input logic        enable_cuenta,
  input logic        write_enable,
  input logic        write_value_reg_en,
  input logic        read_value_reg_en,
  input logic        led_write,
  input logic        led_read,
  input logic [3:0]  estado
);

  // Mirror DUT encodings
  localparam int STATE_0   = 0;
  localparam int STATE_1   = 1;
  localparam int STATE_2   = 2;
  localparam int STATE_3   = 3;
  localparam int STATE_4   = 4;
  localparam int RESET_VAL = 4'hF;

  default clocking cb @(posedge div_clock); endclocking

  // 1) State domain
  ap_state_domain: assert property (cb
    estado inside {RESET_VAL, STATE_0, STATE_1, STATE_2, STATE_3, STATE_4}
  );

  // 2) Reset behavior
  ap_reset_hold: assert property (cb
    reset |-> (estado == RESET_VAL)
  );

  ap_reset_release_to_S0: assert property (cb
    $past(reset) && !reset |-> ($past(estado) == RESET_VAL && estado == STATE_0)
  );

  // 3) Next-state transitions (when not in reset)
  ap_s0_s1: assert property (cb disable iff (reset)
    (estado == STATE_0) |=> (estado == STATE_1)
  );
  ap_s1_s2: assert property (cb disable iff (reset)
    (estado == STATE_1) |=> (estado == STATE_2)
  );
  ap_s2_s3: assert property (cb disable iff (reset)
    (estado == STATE_2) |=> (estado == STATE_3)
  );
  ap_s3_s4: assert property (cb disable iff (reset)
    (estado == STATE_3) |=> (estado == STATE_4)
  );
  ap_s4_s0: assert property (cb disable iff (reset)
    (estado == STATE_4) |=> (estado == STATE_0)
  );
  // If sentinel RESET_VAL observed with reset low, go to S0 next
  ap_rstval_to_s0: assert property (cb disable iff (reset)
    (estado == RESET_VAL) |=> (estado == STATE_0)
  );

  // 4) Output decode equivalence
  ap_enable_cuenta:      assert property (cb enable_cuenta      == (estado == STATE_4));
  ap_write_val_reg_en:   assert property (cb write_value_reg_en == (estado == STATE_1));
  ap_read_val_reg_en:    assert property (cb read_value_reg_en  == (estado == STATE_3));
  ap_write_enable:       assert property (cb write_enable       == (estado != STATE_1));
  ap_write_en_compl:     assert property (cb write_enable       == ~write_value_reg_en);
  ap_led_write:          assert property (cb led_write          == (estado inside {STATE_0,STATE_1,STATE_2}));
  ap_led_read:           assert property (cb led_read           == (estado inside {STATE_3,STATE_4}));
  ap_led_mutual_excl:    assert property (cb !(led_write && led_read));

  // During reset, outputs must match decode of RESET_VAL
  ap_outputs_during_reset: assert property (cb
    reset |-> (!enable_cuenta && write_enable && !write_value_reg_en &&
               !read_value_reg_en && !led_write && !led_read)
  );

  // 5) Functional coverage
  // Visit all functional states (excluding RESET_VAL)
  cp_all_states: cover property (cb disable iff (reset)
    (estado == STATE_0) ##1 (estado == STATE_1) ##1 (estado == STATE_2) ##1
    (estado == STATE_3) ##1 (estado == STATE_4)
  );

  // Full-cycle sequence
  cp_full_cycle: cover property (cb disable iff (reset)
    (estado == STATE_0) ##1 (estado == STATE_1) ##1 (estado == STATE_2) ##1
    (estado == STATE_3) ##1 (estado == STATE_4) ##1 (estado == STATE_0)
  );

  // Reset release into S0
  cp_reset_release: cover property (cb
    $past(reset) && !reset && $past(estado) == RESET_VAL && estado == STATE_0
  );

  // Output pattern coverage per state
  cp_s1_write_phase: cover property (cb disable iff (reset)
    (estado == STATE_1) and (write_value_reg_en && !write_enable && led_write && !led_read)
  );
  cp_s3_read_phase: cover property (cb disable iff (reset)
    (estado == STATE_3) and (read_value_reg_en && write_enable && !led_write && led_read)
  );
  cp_s4_enable_cuenta: cover property (cb disable iff (reset)
    (estado == STATE_4) and (enable_cuenta && write_enable && !led_write && led_read)
  );

endmodule

// Bind into DUT
bind fsm_module fsm_module_sva sva_i (
  .div_clock(div_clock),
  .reset(reset),
  .enable_cuenta(enable_cuenta),
  .write_enable(write_enable),
  .write_value_reg_en(write_value_reg_en),
  .read_value_reg_en(read_value_reg_en),
  .led_write(led_write),
  .led_read(led_read),
  .estado(estado)
);