// SVA for opening_detector and opening3x3
// High-signal-quality, concise checks with essential coverage

// Bind into opening_detector
module opening_detector_sva;
  // Clock/past-valid
  bit past_valid;
  initial past_valid = 0;
  always_ff @(posedge rx_pclk) past_valid <= 1;

  default clocking cb @(posedge rx_pclk); endclocking
  default disable iff (!past_valid);

  // Mask generation forwarded correctly into open3
  assert property (open3.mask == (rx_red == 8'hFF));

  // open3 output registers are 1-cycle registered pass-throughs of inputs
  assert property (open3.out_de     == $past(rx_de));
  assert property (open3.out_hsync  == $past(rx_hsync));
  assert property (open3.out_vsync  == $past(rx_vsync));

  // Top-level passthrough wiring
  assert property (tx_de    == open3.out_de);
  assert property (tx_hsync == open3.out_hsync);
  assert property (tx_vsync == open3.out_vsync);

  // Opening flag temporal behavior vs in_de
  assert property (open3.opened |-> $past(rx_de));
  assert property ($fell(open3.opened) |-> $past(!rx_de));

  // Color pipeline behavior (registered, 1-cycle latency)
  assert property (opening_r == ($past(open3.opened) ? 8'hFF : $past(rx_red)));
  assert property (opening_g == ($past(open3.opened) ? 8'hFF : $past(rx_green)));
  assert property (opening_b == ($past(open3.opened) ? 8'hFF : $past(rx_blue)));

  // TX colors are directly driven from opening_* registers
  assert property (tx_red   == opening_r);
  assert property (tx_green == opening_g);
  assert property (tx_blue  == opening_b);

  // Knownness on outputs
  assert property (!$isunknown({tx_de, tx_hsync, tx_vsync, tx_red, tx_green, tx_blue}));

  // Coverage
  cover property ($rose(rx_de));
  cover property ($fell(rx_de));
  cover property ($rose(open3.opened));
  cover property ($fell(open3.opened));
  cover property ($rose(rx_vsync));
  cover property ($rose(rx_hsync));
endmodule

bind opening_detector opening_detector_sva od_sva_inst();


// Bind into opening3x3 (module-level checks)
module opening3x3_sva;
  // Clock/past-valid
  bit past_valid;
  initial past_valid = 0;
  always_ff @(posedge clk) past_valid <= 1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid || rst);

  // out_* are registered pass-throughs when ce is high
  assert property (ce |-> (out_de == $past(in_de) && out_hsync == $past(in_hsync) && out_vsync == $past(in_vsync)));

  // Hold state and outputs when ce is low
  assert property (!ce |-> $stable({opened, out_de, out_hsync, out_vsync, state}));

  // Reset behavior
  assert property (rst |=> (!opened && !out_de && !out_hsync && !out_vsync));

  // State encoding sanity
  assert property (state inside {[0:2]});

  // State transition correctness (with outputs where assigned)
  assert property ((state == STATE_IDLE   && ce) |=> (mask ? state == STATE_SEARCH : state == STATE_IDLE));
  assert property ((state == STATE_SEARCH && ce) |=> (!mask ? (state == STATE_IDLE && opened == 0)
                                                           : (in_de ? (state == STATE_FOUND && opened == 1)
                                                                    :  state == STATE_SEARCH)));
  assert property ((state == STATE_FOUND  && ce) |=> (!in_de ? (state == STATE_IDLE && opened == 0)
                                                            :  state == STATE_FOUND));

  // Opening flag rise/fall causes
  assert property ($rose(opened) |-> $past(ce && mask && in_de));
  assert property ($fell(opened) |-> $past(!in_de));

  // Coverage: full path IDLE->SEARCH->FOUND->IDLE
  cover property (ce && state == STATE_IDLE ##1 mask ##1 state == STATE_SEARCH ##1 in_de ##1
                  state == STATE_FOUND ##1 !in_de ##1 state == STATE_IDLE);
endmodule

bind opening3x3 opening3x3_sva o3_sva_inst();