// SVA checker for module 'read'
module read_sva (
  input  logic        reset,
  input  logic        readbitclk,
  input  logic        readbitout,
  input  logic        readbitdone,
  input  logic        read_sample_ctl,
  input  logic        read_sample_clk,
  input  logic        read_sample_datain,
  input  logic [15:0] handle,
  input  logic [5:0]  bitoutcounter,
  input  logic        initialized
);
  timeunit 1ns/1ps;

  default clocking cb @(posedge readbitclk); endclocking
  default disable iff (reset);

  // Basic sanity
  assert property (bitoutcounter inside {[6'd0:6'd32]});
  assert property (!$isunknown({readbitout, readbitdone, read_sample_clk, read_sample_ctl, bitoutcounter, initialized}));

  // Done correctness and stability
  assert property (readbitdone == (bitoutcounter == 6'd0));
  assert property (readbitdone |=> (bitoutcounter == 6'd0) and readbitdone);

  // Initialization behavior
  assert property (!initialized |=> initialized and (bitoutcounter == 6'd32) and read_sample_ctl);
  assert property (initialized |=> initialized);

  // Counter next-state behavior
  assert property (initialized && !readbitdone |=> bitoutcounter == $past(bitoutcounter) - 6'd1);

  // Control signal relationship to counter (after init)
  assert property (initialized |-> read_sample_ctl == ((bitoutcounter >= 6'd15) && (bitoutcounter != 6'd0)));

  // Sample clock gating
  assert property (read_sample_clk == (bitoutcounter > 6'd15));                   // at posedge readbitclk
  assert property (@(negedge readbitclk) disable iff (reset) read_sample_clk==0); // low when readbitclk low
  assert property (read_sample_clk |-> read_sample_ctl);                           // clk high implies ctl high

  // readbitout muxing correctness
  assert property ((bitoutcounter == 6'd32) |-> (readbitout == 1'b0));
  assert property (((bitoutcounter > 6'd15) && (bitoutcounter != 6'd32)) |-> (readbitout == read_sample_datain));
  assert property ((bitoutcounter <= 6'd15) |-> (readbitout == handle[bitoutcounter]));

  // Coverage: representative full transaction and key boundaries
  cover property (initialized ##1 (bitoutcounter==6'd32 && readbitout==1'b0)
                  ##1 (bitoutcounter==6'd31 && readbitout==read_sample_datain)
                  ##1 (bitoutcounter==6'd16 && read_sample_clk && read_sample_ctl)
                  ##1 (bitoutcounter==6'd15 && !read_sample_clk && read_sample_ctl && readbitout==handle[15])
                  ##[1:$] readbitdone);

  cover property (bitoutcounter==6'd20 && readbitout==read_sample_datain);
  cover property (bitoutcounter==6'd5  && readbitout==handle[5]);
endmodule

// Bind into DUT
bind read read_sva u_read_sva (.*);