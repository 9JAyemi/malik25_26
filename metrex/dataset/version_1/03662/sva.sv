// SVA for TDC
module TDC_sva #(parameter int resolution = 1);

  default clocking cb @(posedge clk); endclocking
  default disable iff ($isunknown({in1,in2,in1_prev,in2_prev,count,out}));

  // Parameter sanity
  assert property (1 |-> (resolution > 0));

  // Rising-edge detection matches prev-based logic
  assert property ($rose(in1) |-> (in1 && !in1_prev));
  assert property ((in1 && !in1_prev) |-> $rose(in1));
  assert property ($rose(in2) |-> (in2 && !in2_prev));
  assert property ((in2 && !in2_prev) |-> $rose(in2));

  // Start: reset count to 0; out holds
  assert property ($rose(in1) |=> (count == 16'd0));
  assert property ($rose(in1) |=> (out == $past(out)));

  // Stop (without simultaneous start): out updates with elapsed time; count holds
  assert property ($rose(in2) && !$rose(in1) |=> (out == $past(count) * resolution));
  assert property ($rose(in2) && !$rose(in1) |=> (count == $past(count)));

  // Out only changes on stop (and not when simultaneous start)
  assert property ((out != $past(out)) |-> ($rose(in2) && !$rose(in1)));

  // Idle cycles (no start/stop): count increments by 1 (mod 2^16)
  assert property (!( $rose(in1) || $rose(in2) ) |=> (count == $past(count) + 16'd1));

  // Simultaneous start/stop: start wins; count reset; out holds
  assert property ($rose(in1) && $rose(in2) |=> (count == 16'd0 && out == $past(out)));

  // Coverage: typical measurement, zero-interval, simultaneous edges, wraparound during idle
  cover property ($rose(in1) ##[1:$] $rose(in2));
  cover property ($rose(in1) ##1 $rose(in2) ##1 (out == 16'd0));
  cover property ($rose(in1) ##[2:32] $rose(in2) ##1 (out == $past(count) * resolution));
  cover property ($rose(in1) && $rose(in2));
  cover property ((count == 16'hFFFE) && !( $rose(in1) || $rose(in2) )
                  ##1 (count == 16'hFFFF) && !( $rose(in1) || $rose(in2) )
                  ##1 (count == 16'h0000));

endmodule

bind TDC TDC_sva #(.resolution(resolution)) tdc_sva_i();