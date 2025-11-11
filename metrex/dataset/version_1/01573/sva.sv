// SVA for gpio_delayed_trigger
// Bind this file; focuses on concise, high-quality checks and key coverage

module gpio_delayed_trigger_sva;

  default clocking cb @(posedge aclk); endclocking
  default disable iff (!aresetn);

  // Reset effect (on cycle after reset is low)
  ap_reset_regs_zero: assert property ( $past(!aresetn) |-> (int_trig_reg==1'b0 && out_trig==1'b0 && counter==32'd0) );

  // Input sampling pipeline
  ap_pipe0: assert property ( $past(aresetn) |-> (int_data_reg[0] == $past(int_data_wire)) );
  ap_pipe1: assert property ( $past(aresetn) |-> (int_data_reg[1] == $past(int_data_reg[0])) );

  // Instant trigger set and stickiness
  ap_instant_set_soft: assert property ( (!int_trig_reg && soft_trig) |=> int_trig_reg );
  ap_instant_set_gpio: assert property ( (!int_trig_reg && int_data_reg[1][0]) |=> int_trig_reg );
  ap_instant_sticky:   assert property ( int_trig_reg |=> int_trig_reg );

  // Counter behavior
  ap_count_inc:  assert property ( int_trig_reg && (counter < delay) |=> counter == $past(counter) + 1 );
  ap_count_hold: assert property ( (!int_trig_reg || !(counter < delay)) |=> counter == $past(counter) );

  // Delayed trigger behavior and stickiness
  ap_out_set:    assert property ( !(counter < delay) |=> out_trig );
  ap_out_sticky: assert property ( out_trig |=> out_trig );

  // Output equivalences
  ap_trig_eq: assert property ( trigger == out_trig );
  ap_inst_eq: assert property ( instant_trigger == int_trig_reg );
  ap_dp_eq:   assert property ( delay_pulse == (instant_trigger && !trigger) );

  // int_output encoding
  ap_int_output_lsb: assert property ( int_output[0] == delay_pulse );
  generate if (GPIO_OUTPUT_WIDTH > 1) begin
    ap_int_output_msbs_zero: assert property ( int_output[GPIO_OUTPUT_WIDTH-1:1] == '0 );
  end endgenerate

  // int_data_wire mapping
  generate if (GPIO_INPUT_WIDTH > 0) begin
    ap_in_bus_map:  assert property ( int_data_wire[GPIO_INPUT_WIDTH-1:0] == gpio_data[GPIO_INPUT_WIDTH-1:0] );
  end endgenerate
  generate if (GPIO_OUTPUT_WIDTH > 0) begin
    ap_out_bus_map: assert property ( int_data_wire[GPIO_INPUT_WIDTH +: GPIO_OUTPUT_WIDTH] == out_data );
  end endgenerate
  generate if (GPIO_DATA_WIDTH > GPIO_INPUT_WIDTH + GPIO_OUTPUT_WIDTH) begin
    localparam int PADW = GPIO_DATA_WIDTH - GPIO_INPUT_WIDTH - GPIO_OUTPUT_WIDTH;
    ap_tail_zero: assert property ( int_data_wire[GPIO_INPUT_WIDTH+GPIO_OUTPUT_WIDTH +: PADW] == '0 );
  end endgenerate

  // Key coverage
  cp_soft_path:  cover property ( $rose(soft_trig) ##1 int_trig_reg );
  cp_gpio_path:  cover property ( $rose(gpio_data[0]) ##2 int_trig_reg );
  cp_delay_done: cover property ( int_trig_reg && (counter < delay)[*1:$] ##1 out_trig );
  cp_zero_delay: cover property ( (delay==0) ##1 out_trig );

endmodule

bind gpio_delayed_trigger gpio_delayed_trigger_sva sva_gpio_delayed_trigger();