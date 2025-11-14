// SVA checker for xadc_data_demux
module xadc_data_demux_sva (
  input             clk,
  input             reset,
  input      [15:0] xadc_data,
  input             xadc_data_ready,
  input      [4:0]  channel,
  input      [15:0] xadc_vaux0_data,
  input             xadc_vaux0_ready,
  input      [15:0] xadc_vaux8_data,
  input             xadc_vaux8_ready
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Ready flags are exact functions of inputs (outside reset)
  assert property (xadc_vaux0_ready == (xadc_data_ready && (channel == 5'h10)));
  assert property (xadc_vaux8_ready == (xadc_data_ready && (channel == 5'h18)));

  // On a ready, corresponding data updates to the sampled input
  assert property (xadc_vaux0_ready |=> (xadc_vaux0_data == $past(xadc_data)));
  assert property (xadc_vaux8_ready |=> (xadc_vaux8_data == $past(xadc_data)));

  // Without ready, data holds its previous value
  assert property (!xadc_vaux0_ready |=> $stable(xadc_vaux0_data));
  assert property (!xadc_vaux8_ready |=> $stable(xadc_vaux8_data));

  // Reset behavior (checked during reset)
  assert property (@(posedge clk)
    reset |-> (xadc_vaux0_ready==1'b0 && xadc_vaux8_ready==1'b0 &&
               xadc_vaux0_data==16'd0  && xadc_vaux8_data==16'd0));

  // Basic functional coverage
  cover property (@(posedge clk) !reset ##1 xadc_vaux0_ready);
  cover property (@(posedge clk) !reset ##1 xadc_vaux8_ready);
  cover property (@(posedge clk) !reset ##1 xadc_vaux0_ready ##1 xadc_vaux8_ready);
  cover property (@(posedge clk) !reset ##1 xadc_vaux8_ready ##1 xadc_vaux0_ready);
  cover property (@(posedge clk) !reset ##1 xadc_vaux0_ready ##1 xadc_vaux0_ready);
  cover property (@(posedge clk) !reset ##1 xadc_vaux8_ready ##1 xadc_vaux8_ready);
  cover property (@(posedge clk) !reset ##1 (xadc_data_ready && !(channel inside {5'h10,5'h18})));

endmodule

// Example bind (in your testbench or a package):
// bind xadc_data_demux xadc_data_demux_sva sva (.*);