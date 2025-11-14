// SVA for rcv: bindable, concise, and focused on key behavior

module rcv_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        full,
  input  logic [7:0]  parallel_out,
  input  logic        serial_in,
  input  logic        serial_p,
  input  logic        serial_s,
  input  logic [3:0]  state,
  input  logic [8:0]  shift,
  input  logic [10:0] count
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Synchronizer correctness
  assert property (serial_p == $past(serial_in));
  assert property (serial_s == $past(serial_p));

  // State legality
  assert property (state inside {[4'h0:4'hb]});

  // full is asserted only in state==b and is a 1-cycle pulse
  assert property (full |-> state == 4'hb);
  assert property (state == 4'hb |-> full);
  assert property (full |=> !full);

  // Idle behavior and start detection
  assert property ((state == 4'h0 && serial_s == 1'b1) |=> state == 4'h0 && full == 1'b0 && $stable(count));
  assert property ((state == 4'h0 && serial_s == 1'b0) |=> state == 4'h1 && count == 11'd651);

  // First sampling occurs exactly 651 cycles after start
  assert property ((state == 4'h0 && serial_s == 1'b0) |=> ##651 (state == 4'h1 && count == 11'd0));

  // Bit period: for states 1..9, next sampling exactly 1302 cycles later and state increments
  assert property ((state inside {[4'h1:4'h9]} && count == 11'd0) |=> ##1302 (count == 11'd0 && state == $past(state)+4'd1));

  // Counter/shift behavior within data/stop collection states
  assert property ((state inside {[4'h1:4'ha]} && count > 11'd0) |=> count == $past(count)-11'd1 && state == $past(state) && $stable(shift));
  assert property ((state inside {[4'h1:4'ha]} && count == 11'd0) |=> count == 11'd1302 && state == $past(state)+4'd1 && shift == { $past(serial_s), $past(shift[8:1]) });

  // End of frame handling
  assert property ((state == 4'ha && count == 11'd0) |=> state == 4'hb);
  assert property ((state == 4'hb) |=> state == 4'h0);

  // Shift updates only on sampling events
  assert property (!(state inside {[4'h1:4'ha]} && count == 11'd0) |=> $stable(shift));

  // Data ordering: parallel_out matches the last 8 sampled bits (LSB first) at full
  sequence samp_evt; (state inside {[4'h1:4'ha]}) && (count == 11'd0); endsequence
  property p_data_order;
    bit s1,s2,s3,s4,s5,s6,s7,s8,s9,s10;
    (samp_evt, s1 = serial_s)
    ##[1:$] (samp_evt, s2 = serial_s)
    ##[1:$] (samp_evt, s3 = serial_s)
    ##[1:$] (samp_evt, s4 = serial_s)
    ##[1:$] (samp_evt, s5 = serial_s)
    ##[1:$] (samp_evt, s6 = serial_s)
    ##[1:$] (samp_evt, s7 = serial_s)
    ##[1:$] (samp_evt, s8 = serial_s)
    ##[1:$] (samp_evt, s9 = serial_s)
    ##[1:$] (samp_evt, s10 = serial_s)
    |=> (state == 4'hb && full && parallel_out == {s9,s8,s7,s6,s5,s4,s3,s2});
  endproperty
  assert property (p_data_order);

  // Basic coverage

  // Exercise all states
  cover property (state == 4'h0);
  cover property (state == 4'h1);
  cover property (state == 4'h2);
  cover property (state == 4'h3);
  cover property (state == 4'h4);
  cover property (state == 4'h5);
  cover property (state == 4'h6);
  cover property (state == 4'h7);
  cover property (state == 4'h8);
  cover property (state == 4'h9);
  cover property (state == 4'ha);
  cover property (state == 4'hb);

  // A complete frame: start detected -> first sample -> final full pulse
  cover property ((state == 4'h0 && serial_s == 1'b0)
                  ##651 (state == 4'h1 && count == 11'd0)
                  ##[1:$] (state == 4'hb && full));

  // Back-to-back frames (two full pulses separated by idle)
  cover property ($rose(full) ##[1:$] (state == 4'h0) ##[1:$] $rose(full));

endmodule

bind rcv rcv_sva i_rcv_sva (.*);