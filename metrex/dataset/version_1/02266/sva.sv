// SVA checker for i2s
module i2s_sva #(parameter CLK_DIVISOR = 6) ();

  // Clocking/reset are taken from the bound scope
  // Assertions use hierarchical references to the bound i2s instance signals.

  // Divider/counting and audio_clock behavior
  assert property (@(posedge clk_i) disable iff (rst_i)
    audio_clock_div < CLK_DIVISOR);

  assert property (@(posedge clk_i) disable iff (rst_i)
    (audio_clock_div == CLK_DIVISOR-1) |=> (audio_clock_div == 0 && audio_clock != $past(audio_clock)));

  assert property (@(posedge clk_i) disable iff (rst_i)
    (audio_clock_div != CLK_DIVISOR-1) |=> (audio_clock_div == $past(audio_clock_div)+1 && audio_clock == $past(audio_clock)));

  // prev_audio_clock tracks 1-cycle delayed audio_clock
  assert property (@(posedge clk_i) disable iff (rst_i)
    prev_audio_clock == $past(audio_clock));

  // bclk_o follows audio_clock edges and only changes on audio_clock edges
  assert property (@(posedge clk_i) disable iff (rst_i) $rose(audio_clock) |=> bclk_o);
  assert property (@(posedge clk_i) disable iff (rst_i) $fell(audio_clock) |=> !bclk_o);
  assert property (@(posedge clk_i) disable iff (rst_i) $changed(bclk_o) |-> ($rose(audio_clock) || $fell(audio_clock)));

  // ws_o is combinational of word_sel; word_sel only toggles at start of a 16-bit word
  assert property (@(posedge clk_i) ws_o == word_sel);
  assert property (@(posedge clk_i) disable iff (rst_i)
    ($fell(audio_clock) && bit_count==0) |=> (word_sel == !$past(word_sel)));
  assert property (@(posedge clk_i) disable iff (rst_i)
    $changed(word_sel) |-> $past($fell(audio_clock) && bit_count==0));

  // data_o only updates on falling audio_clock edges
  assert property (@(posedge clk_i) disable iff (rst_i)
    $changed(data_o) |-> $fell(audio_clock));

  // At each falling edge, data_o equals MSB of selected shift register
  assert property (@(posedge clk_i) disable iff (rst_i)
    ($fell(audio_clock) && bit_count==0) |-> data_o == (word_sel ? input_reg1[15] : input_reg0[15]));
  assert property (@(posedge clk_i) disable iff (rst_i)
    ($fell(audio_clock) && bit_count!=0) |-> data_o == (word_sel ? input_reg1[15] : input_reg0[15]));

  // Shift behavior on middle bits
  assert property (@(posedge clk_i) disable iff (rst_i)
    ($fell(audio_clock) && bit_count!=0 && !word_sel) |=> input_reg0 == {$past(input_reg0[14:0]),1'b0});
  assert property (@(posedge clk_i) disable iff (rst_i)
    ($fell(audio_clock) && bit_count!=0 &&  word_sel) |=> input_reg1 == {$past(input_reg1[14:0]),1'b0});

  // bit_count progression on each falling edge
  assert property (@(posedge clk_i) disable iff (rst_i)
    ($fell(audio_clock) && bit_count==0) |=> bit_count==1);
  assert property (@(posedge clk_i) disable iff (rst_i)
    ($fell(audio_clock) && bit_count!=0 && bit_count!=15) |=> bit_count == $past(bit_count)+1);
  assert property (@(posedge clk_i) disable iff (rst_i)
    ($fell(audio_clock) && bit_count==15) |=> bit_count==0);

  // FIFO handshake: rd/ur only at start of word, mutually exclusive, 1-cycle pulses
  assert property (@(posedge clk_i) disable iff (rst_i)
    pcm_fifo_rd_o |-> ($fell(audio_clock) && bit_count==0 && !pcm_fifo_empty_i));
  assert property (@(posedge clk_i) disable iff (rst_i)
    pcm_fifo_ur_o |-> ($fell(audio_clock) && bit_count==0 &&  pcm_fifo_empty_i));
  assert property (@(posedge clk_i) disable iff (rst_i)
    !(pcm_fifo_rd_o && pcm_fifo_ur_o));
  assert property (@(posedge clk_i) disable iff (rst_i)
    pcm_fifo_rd_o |=> !pcm_fifo_rd_o);
  assert property (@(posedge clk_i) disable iff (rst_i)
    pcm_fifo_ur_o |=> !pcm_fifo_ur_o);

  // Register/load behavior at start of word
  assert property (@(posedge clk_i) disable iff (rst_i)
    ($fell(audio_clock) && bit_count==0 && !pcm_fifo_empty_i)
      |=> (input_reg0 == $past(pcm_data_i[31:16]) && input_reg1 == $past(pcm_data_i[15:0]) && pcm_data_last == $past(pcm_data_i)));
  assert property (@(posedge clk_i) disable iff (rst_i)
    ($fell(audio_clock) && bit_count==0 && pcm_fifo_empty_i)
      |=> (input_reg0 == $past(pcm_data_last[31:16]) && input_reg1 == $past(pcm_data_last[15:0]) && pcm_data_last == $past(pcm_data_last)));

  // Functional coverage
  cover property (@(posedge clk_i) disable iff (rst_i)
    ($fell(audio_clock) && bit_count==0 && !pcm_fifo_empty_i)); // normal read
  cover property (@(posedge clk_i) disable iff (rst_i)
    ($fell(audio_clock) && bit_count==0 && pcm_fifo_empty_i));  // underflow reuse
  // Cover two full 16-bit words back-to-back (both channels toggle)
  cover property (@(posedge clk_i) disable iff (rst_i)
    ($fell(audio_clock) && bit_count==0)
    ##1 (($fell(audio_clock))[*15])
    ##1 ($fell(audio_clock) && bit_count==0)
    ##1 (($fell(audio_clock))[*15])
    ##1 ($fell(audio_clock) && bit_count==0));

endmodule

// Example bind (put in a testbench or a package included in sim)
// Binds into all i2s instances and connects to internal nets by name.
bind i2s i2s_sva #(.CLK_DIVISOR(CLK_DIVISOR)) i2s_sva_i();