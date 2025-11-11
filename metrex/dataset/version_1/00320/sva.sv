// SVA for ddr3_int_ex_lfsr8
// Bind this checker to the DUT for concise, high-quality functional checking and coverage.

module ddr3_int_ex_lfsr8_sva #(parameter seed = 32)
(
  input  logic        clk,
  input  logic        reset_n,
  input  logic        enable,
  input  logic        pause,
  input  logic        load,
  input  logic [7:0]  ldata,
  input  logic [7:0]  data
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  assert property (cb disable iff (!reset_n) !$isunknown(data));

  // Asynchronous reset drives seed by next clock
  assert property (cb (!reset_n) |=> data == seed[7:0]);

  // !enable has priority over load/pause: force seed next cycle
  assert property (cb disable iff (!reset_n) (!enable) |=> data == seed[7:0]);

  // load (when enabled) takes effect next cycle, regardless of pause
  assert property (cb disable iff (!reset_n) (enable && load) |=> data == ldata);

  // pause holds value (when enabled and not loading)
  assert property (cb disable iff (!reset_n) (enable && !load && pause) |=> data == $past(data));

  // LFSR next-state function when enabled, not loading, not paused
  assert property (cb disable iff (!reset_n)
    (enable && !load && !pause) |=> data ==
      { $past(data[6]),
        $past(data[5]),
        $past(data[4]),
        $past(data[3]) ^ $past(data[7]),
        $past(data[2]) ^ $past(data[7]),
        $past(data[1]) ^ $past(data[7]),
        $past(data[0]),
        $past(data[7]) }
  );

  // Coverage: exercise key behaviors
  // 1) Reset then shift a few steps
  cover property (cb !reset_n ##1 reset_n ##1 (enable && !load && !pause)[*4]);

  // 2) Load path observed
  cover property (cb disable iff (!reset_n) (enable && load) ##1 (data == $past(ldata)));

  // 3) Pause holds for two cycles
  cover property (cb disable iff (!reset_n)
    (enable && !load && pause) ##1 (data == $past(data)) ##1 (data == $past(data,2)));

  // 4) Disable forces seed
  cover property (cb disable iff (!reset_n) (!enable) ##1 (data == seed[7:0]));

endmodule

bind ddr3_int_ex_lfsr8 ddr3_int_ex_lfsr8_sva #(.seed(seed)) i_ddr3_int_ex_lfsr8_sva
(
  .clk    (clk),
  .reset_n(reset_n),
  .enable (enable),
  .pause  (pause),
  .load   (load),
  .ldata  (ldata),
  .data   (data)
);