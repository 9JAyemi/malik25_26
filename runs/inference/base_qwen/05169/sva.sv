module sequence_counter_sva (
  input logic slowest_sync_clk,
  input logic lpf_int,
  output logic Core,
  output logic bsr,
  output logic pr
);
  // Counter for 100MHz clock
  // Core signal is set to 1 every 100MHz cycle
  counter_100MHz: assert property (
    @(posedge slowest_sync_clk) disable iff (!lpf_int) Core == (cnt_100M == 100_000_000)
  );

  // Counter for Core signal
  // bsr signal is set to 1 every 256 cycles of Core
  counter_core: assert property (
    @(posedge lpf_int) disable iff (!lpf_int) bsr == (cnt_core == 256)
  );

  // Counter for bsr signal
  // pr signal is set to 1 every 64 cycles of bsr
  counter_bsr: assert property (
    @(posedge lpf_int) disable iff (!lpf_int) pr == (cnt_bsr == 64)
  );
endmodule