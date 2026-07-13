module priority_encoder_led_display_sva (
  input logic [3:0] data,
  input logic [3:0] led_display
);

  // Data 0001 maps to led_display 1.
  check_map_0001_to_1: assert property (
    @(posedge data[0]) (data == 4'b0001) |-> (led_display == 4'd1)
  );

  // Data 0010 maps to led_display 2.
  check_map_0010_to_2: assert property (
    @(posedge data[0]) (data == 4'b0010) |-> (led_display == 4'd2)
  );

  // Data 0100 maps to led_display 3.
  check_map_0100_to_3: assert property (
    @(posedge data[0]) (data == 4'b0100) |-> (led_display == 4'd3)
  );

  // Data 1000 maps to led_display 4.
  check_map_1000_to_4: assert property (
    @(posedge data[0]) (data == 4'b1000) |-> (led_display == 4'd4)
  );

  // Any non-listed data value maps to 0.
  check_default_zero_for_others: assert property (
    @(posedge data[0]) (data != 4'b0001 && data != 4'b0010 && data != 4'b0100 && data != 4'b1000) |-> (led_display == 4'd0)
  );

  // Output is always one of {0,1,2,3,4}.
  check_output_value_set: assert property (
    @(posedge data[0]) (led_display inside {4'd0,4'd1,4'd2,4'd3,4'd4})
  );

  // led_display 1 occurs only when data is 0001.
  check_rev_1_implies_0001: assert property (
    @(posedge data[0]) (led_display == 4'd1) |-> (data == 4'b0001)
  );

  // led_display 2 occurs only when data is 0010.
  check_rev_2_implies_0010: assert property (
    @(posedge data[0]) (led_display == 4'd2) |-> (data == 4'b0010)
  );

  // led_display 3 occurs only when data is 0100.
  check_rev_3_implies_0100: assert property (
    @(posedge data[0]) (led_display == 4'd3) |-> (data == 4'b0100)
  );

  // led_display 4 occurs only when data is 1000.
  check_rev_4_implies_1000: assert property (
    @(posedge data[0]) (led_display == 4'd4) |-> (data == 4'b1000)
  );

  // Output contains no X/Z.
  check_output_never_unknown: assert property (
    @(posedge data[0]) !$isunknown(led_display)
  );

endmodule