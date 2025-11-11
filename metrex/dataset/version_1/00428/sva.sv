// SVA for oh_dsync: concise, high-quality checks and coverage
// Bindable to all instances; handles both CFG_ASIC and RTL versions.

module oh_dsync_sva #(parameter int PS=2, parameter int DELAY=0)
(
  input logic clk,
  input logic nreset,
  input logic din,
  input logic dout
);

  default clocking cb @(posedge clk); endclocking

  // Parameter guards
  initial begin
    assert (DELAY inside {0,1}) else $error("oh_dsync: DELAY must be 0 or 1");
    if (DELAY==0) assert (PS>=1) else $error("oh_dsync: PS must be >=1 when DELAY==0");
  end

  localparam int IDX = (DELAY ? PS : PS-1);
  localparam int L   = IDX + 1;

  // Reset behavior
  a_reset_dout_zero: assert property (cb (!nreset |-> (dout==1'b0)));
  a_no_x_dout:       assert property (cb disable iff (!nreset) !$isunknown(dout));

`ifndef CFG_ASIC
  // Internal pipe checks (only for RTL path)
  a_reset_pipe_zero: assert property (cb (!nreset |-> (sync_pipe=='0)));
  a_no_x_pipe:       assert property (cb disable iff (!nreset) !$isunknown(sync_pipe));

  // Shift behavior (guard PS>0 for part-select legality)
  generate if (PS>0) begin
    a_shift: assert property (cb disable iff (!nreset)
                              sync_pipe == { $past(sync_pipe[PS-1:0]), $past(din) });
  end endgenerate

  // Output mapping (avoid illegal indices via generate)
  generate
    if (DELAY==0) begin
      a_map0: assert property (cb dout == sync_pipe[PS-1]);
    end else begin
      a_map1: assert property (cb dout == sync_pipe[PS]);
    end
  endgenerate
`endif

  // Exact latency check vs din (independent of internal implementation)
  sequence ready_L; nreset[*L]; endsequence
  a_latency_exact: assert property (cb disable iff (!nreset)
                                    ready_L |-> (dout == $past(din, L)));

  // Edge propagation coverage
  c_rise: cover property (cb disable iff (!nreset) $rose(din) ##L $rose(dout));
  c_fall: cover property (cb disable iff (!nreset) $fell(din) ##L $fell(dout));

endmodule

// Bind to all oh_dsync instances, inheriting their parameters
bind oh_dsync oh_dsync_sva #(.PS(PS), .DELAY(DELAY))
  oh_dsync_sva_b (.clk(clk), .nreset(nreset), .din(din), .dout(dout));