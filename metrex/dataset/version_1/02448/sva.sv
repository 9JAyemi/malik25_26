// SVA for i2s_shift_in
// Bind this checker to the DUT
bind i2s_shift_in i2s_shift_in_sva sva ();

module i2s_shift_in_sva ();
  // Access bound instance signals
  // (Elaboration is in the scope of i2s_shift_in, so names resolve locally)
  logic         clk, reset_n, enable, bclk, lrclk, data_in, fifo_ready, fifo_write;
  logic [31:0]  fifo_right_data, fifo_left_data, shift_register;

  // Implicit connections to bound scope
  assign clk             = i2s_shift_in.clk;
  assign reset_n         = i2s_shift_in.reset_n;
  assign enable          = i2s_shift_in.enable;
  assign bclk            = i2s_shift_in.bclk;
  assign lrclk           = i2s_shift_in.lrclk;
  assign data_in         = i2s_shift_in.data_in;
  assign fifo_ready      = i2s_shift_in.fifo_ready;
  assign fifo_write      = i2s_shift_in.fifo_write;
  assign fifo_left_data  = i2s_shift_in.fifo_left_data;
  assign fifo_right_data = i2s_shift_in.fifo_right_data;
  assign shift_register  = i2s_shift_in.shift_register;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n);

  // Re-create DUT's edge detection and "first falling" pulses
  logic bclk_q, lrclk_q;
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      bclk_q <= 1'b0;
      lrclk_q <= 1'b0;
    end else begin
      bclk_q <= bclk;
      lrclk_q <= lrclk;
    end
  end
  wire bclk_re =  bclk & ~bclk_q;
  wire bclk_fe = ~bclk &  bclk_q;
  wire lr_re   =  lrclk & ~lrclk_q;
  wire lr_fe   = ~lrclk &  lrclk_q;

  // First BCLK falling edge after LR rising/falling (with an intervening BCLK rising)
  logic [1:0] s_after_lr_rise, s_after_lr_fall;
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      s_after_lr_rise <= 2'b00;
      s_after_lr_fall <= 2'b00;
    end else begin
      // LR rising path (left capture)
      if (lr_re)                                     s_after_lr_rise <= 2'b01;
      else if (s_after_lr_rise == 2'b01 && bclk_re)  s_after_lr_rise <= 2'b10;
      else if (s_after_lr_rise == 2'b10 && bclk_fe)  s_after_lr_rise <= 2'b11;
      else if (s_after_lr_rise == 2'b11)             s_after_lr_rise <= 2'b00;

      // LR falling path (right capture)
      if (lr_fe)                                     s_after_lr_fall <= 2'b01;
      else if (s_after_lr_fall == 2'b01 && bclk_re)  s_after_lr_fall <= 2'b10;
      else if (s_after_lr_fall == 2'b10 && bclk_fe)  s_after_lr_fall <= 2'b11;
      else if (s_after_lr_fall == 2'b11)             s_after_lr_fall <= 2'b00;
    end
  end
  wire lcap_pulse = (s_after_lr_rise == 2'b11);
  wire rcap_pulse = (s_after_lr_fall == 2'b11);

  // Basic sanity
  assert property ( !(bclk_re && bclk_fe) );
  assert property ( !(lr_re   && lr_fe)   );
  assert property ( !(lcap_pulse && rcap_pulse) );
  assert property ( lcap_pulse |-> !$past(lcap_pulse) ##1 !lcap_pulse );
  assert property ( rcap_pulse |-> !$past(rcap_pulse) ##1 !rcap_pulse );

  // Reset/enable behavior
  assert property ( !reset_n |-> shift_register==0 && fifo_left_data==0 && fifo_right_data==0 && fifo_write==0 );
  assert property ( !enable  |-> shift_register==0 && fifo_left_data==0 && fifo_right_data==0 && fifo_write==0 );

  // Shift behavior
  assert property ( enable && bclk_re  |-> shift_register == { $past(shift_register)[30:0], $past(data_in) } );
  assert property ( enable && !bclk_re |-> $stable(shift_register) );

  // Data capture to FIFOs
  // Next cycle after the pulse: if still enabled, capture equals prior shift_register; if disabled, FIFO is 0
  assert property ( lcap_pulse |=> ( enable ? fifo_left_data  == $past(shift_register) : fifo_left_data  == 32'h0 ) );
  assert property ( rcap_pulse |=> ( enable ? fifo_right_data == $past(shift_register) : fifo_right_data == 32'h0 ) );

  // FIFO data only changes when its corresponding capture pulse occurred in the previous cycle (and enabled)
  assert property ( fifo_left_data  != $past(fifo_left_data)  |-> $past(enable && lcap_pulse) );
  assert property ( fifo_right_data != $past(fifo_right_data) |-> $past(enable && rcap_pulse) );

  // fifo_write behavior and gating
  assert property ( fifo_write == (enable && fifo_ready && rcap_pulse) );
  assert property ( (!enable || !fifo_ready) |-> !fifo_write );

  // Coverage
  cover property ( enable && lr_re  ##[1:$] bclk_re ##[1:$] bclk_fe ##1 fifo_left_data == $past(shift_register) );
  cover property ( enable && fifo_ready && lr_fe ##[1:$] bclk_re ##[1:$] bclk_fe && fifo_write );
  cover property ( enable && bclk_re && data_in==1'b0 );
  cover property ( enable && bclk_re && data_in==1'b1 );
  cover property ( !enable ##1 enable ##[1:$] (rcap_pulse && fifo_ready && fifo_write) );
endmodule