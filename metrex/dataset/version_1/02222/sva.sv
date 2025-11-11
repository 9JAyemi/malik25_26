// SVA for daala_idct4_stream_v1_0_S00_AXIS
// Focus: protocol correctness, state/ptr invariants, write control, and useful coverage.
// Bind this file to the DUT for maximal checking.

module daala_idct4_stream_v1_0_S00_AXIS_sva #(
  parameter int C_S_AXIS_TDATA_WIDTH = 32,
  parameter int NUMBER_OF_INPUT_WORDS = 8
)(
  input  logic                            S_AXIS_ACLK,
  input  logic                            S_AXIS_ARESETN,
  input  logic                            S_AXIS_TREADY,
  input  logic [C_S_AXIS_TDATA_WIDTH-1:0] S_AXIS_TDATA,
  input  logic [(C_S_AXIS_TDATA_WIDTH/8)-1:0] S_AXIS_TSTRB,
  input  logic                            S_AXIS_TLAST,
  input  logic                            S_AXIS_TVALID,

  // Internal DUT signals (connect via bind)
  input  logic                            mst_exec_state,
  input  logic                            writes_done,
  input  logic                            fifo_wren,
  input  logic [15:0]                     write_pointer
);

  localparam int N = NUMBER_OF_INPUT_WORDS;

  default clocking cb @(posedge S_AXIS_ACLK); endclocking

  // AXI4-Stream master-side assumptions (inputs to DUT)
  // Stable payload while TVALID high and TREADY low
  assume property (disable iff (!S_AXIS_ARESETN)
    S_AXIS_TVALID && !S_AXIS_TREADY |-> $stable({S_AXIS_TDATA,S_AXIS_TSTRB,S_AXIS_TLAST,S_AXIS_TVALID})
  );
  // TLAST only meaningful when TVALID
  assume property (disable iff (!S_AXIS_ARESETN)
    S_AXIS_TLAST |-> S_AXIS_TVALID
  );

  // Reset state
  assert property (!S_AXIS_ARESETN |-> (mst_exec_state==1'b0 && write_pointer==0 && writes_done==1'b0 && S_AXIS_TREADY==1'b0));

  // Ready gating matches spec formula
  assert property (S_AXIS_TREADY == ((mst_exec_state==1'b1) && (write_pointer <= N-1)));

  // fifo_wren equals handshake
  assert property (fifo_wren == (S_AXIS_TVALID && S_AXIS_TREADY));

  // State transitions
  assert property (disable iff (!S_AXIS_ARESETN)
    (mst_exec_state==1'b0 &&  S_AXIS_TVALID) |=> (mst_exec_state==1'b1)
  );
  assert property (disable iff (!S_AXIS_ARESETN)
    (mst_exec_state==1'b0 && !S_AXIS_TVALID) |=> (mst_exec_state==1'b0)
  );
  assert property (disable iff (!S_AXIS_ARESETN)
    (mst_exec_state==1'b1 &&  writes_done)   |=> (mst_exec_state==1'b0)
  );
  assert property (disable iff (!S_AXIS_ARESETN)
    (mst_exec_state==1'b1 && !writes_done)   |=> (mst_exec_state==1'b1)
  );
  // TREADY must be low in IDLE
  assert property (disable iff (!S_AXIS_ARESETN)
    (mst_exec_state==1'b0) |-> !S_AXIS_TREADY
  );

  // Write pointer behavior
  assert property (disable iff (!S_AXIS_ARESETN)
    fifo_wren |=> write_pointer == $past(write_pointer)+1
  );
  assert property (disable iff (!S_AXIS_ARESETN)
    !fifo_wren |=> write_pointer == $past(write_pointer)
  );
  // Pointer never used out-of-range on write; never exceeds N
  assert property (disable iff (!S_AXIS_ARESETN)
    fifo_wren |-> write_pointer <= N-1
  );
  assert property (disable iff (!S_AXIS_ARESETN)
    write_pointer <= N
  );

  // writes_done semantics: only after a completed transfer that ends the frame
  assert property (disable iff (!S_AXIS_ARESETN)
    fifo_wren && (write_pointer==N-1 || S_AXIS_TLAST) |=> writes_done
  );
  assert property (disable iff (!S_AXIS_ARESETN)
    $rose(writes_done) |-> $past(fifo_wren) && ($past(write_pointer)==N-1 || $past(S_AXIS_TLAST))
  );
  // After writes_done in WRITE_FIFO, next state must be IDLE and TREADY low
  assert property (disable iff (!S_AXIS_ARESETN)
    (mst_exec_state==1'b1 && $rose(writes_done)) |=> (mst_exec_state==1'b0 && !S_AXIS_TREADY)
  );

  // Coverage: typical/edge scenarios
  // 1) Full N-beat frame without TLAST before last beat
  cover property (disable iff (!S_AXIS_ARESETN)
    (mst_exec_state==1'b0 && S_AXIS_TVALID)
    ##1 (mst_exec_state==1'b1)
    ##0 (!S_AXIS_TLAST throughout [* (N-1)]) and
    (fifo_wren [* (N-1)])
    ##1 (fifo_wren && write_pointer==N-1 && !S_AXIS_TLAST)
    ##1 writes_done
  );

  // 2) Early TLAST before reaching last element
  cover property (disable iff (!S_AXIS_ARESETN)
    (mst_exec_state==1'b1)
    ##[1:$] (fifo_wren && write_pointer < N-1 && S_AXIS_TLAST)
    ##1 writes_done
  );

  // 3) TLAST coincident with final beat
  cover property (disable iff (!S_AXIS_ARESETN)
    (mst_exec_state==1'b1)
    ##[1:$] (fifo_wren && write_pointer==N-1 && S_AXIS_TLAST)
    ##1 writes_done
  );

  // 4) Backpressure: TVALID held while TREADY deasserted, then accept one beat
  cover property (disable iff (!S_AXIS_ARESETN)
    S_AXIS_TVALID && !S_AXIS_TREADY [*3]
    ##1 (S_AXIS_TVALID && S_AXIS_TREADY)
  );

endmodule


// Bind example (instantiate once per DUT instance)
bind daala_idct4_stream_v1_0_S00_AXIS
  daala_idct4_stream_v1_0_S00_AXIS_sva #(
    .C_S_AXIS_TDATA_WIDTH(C_S_AXIS_TDATA_WIDTH),
    .NUMBER_OF_INPUT_WORDS(8)
  ) dut_sva (
    .S_AXIS_ACLK    (S_AXIS_ACLK),
    .S_AXIS_ARESETN (S_AXIS_ARESETN),
    .S_AXIS_TREADY  (S_AXIS_TREADY),
    .S_AXIS_TDATA   (S_AXIS_TDATA),
    .S_AXIS_TSTRB   (S_AXIS_TSTRB),
    .S_AXIS_TLAST   (S_AXIS_TLAST),
    .S_AXIS_TVALID  (S_AXIS_TVALID),

    .mst_exec_state (mst_exec_state),
    .writes_done    (writes_done),
    .fifo_wren      (fifo_wren),
    .write_pointer  (write_pointer)
  );