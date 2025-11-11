// SVA for daala_4x4_transpose_v1_0_S00_AXIS
// Concise checks of FSM, handshake, counters, and termination; includes key coverage.

module daala_4x4_transpose_sva #(parameter int C_S_AXIS_TDATA_WIDTH = 32,
                                 parameter int N = 8) // NUMBER_OF_INPUT_WORDS
(
  input  logic                     clk,
  input  logic                     rst_n,
  input  logic                     S_AXIS_TVALID,
  input  logic                     S_AXIS_TLAST,
  input  logic                     S_AXIS_TREADY,
  input  logic                     mst_exec_state,  // 0: IDLE, 1: WRITE_FIFO
  input  logic [31:0]              write_pointer,   // widened for compare
  input  logic                     writes_done,
  input  logic                     fifo_wren
);

  localparam int LAST = N-1;

  // Static parameter sanity
  initial begin
    assert ((C_S_AXIS_TDATA_WIDTH % 8) == 0)
      else $error("C_S_AXIS_TDATA_WIDTH must be a multiple of 8");
    assert (N > 0) else $error("N must be > 0");
  end

  default clocking cb @(posedge clk); endclocking

  // Reset values (checked when reset asserted)
  property p_reset_values;
    (!rst_n) |=> (mst_exec_state == 1'b0 && writes_done == 1'b0 && write_pointer == 0 && S_AXIS_TREADY == 1'b0);
  endproperty
  assert property (p_reset_values);

  // FSM transitions
  default disable iff (!rst_n)
  // IDLE hold/leave
  assert property ( (mst_exec_state==1'b0 && !S_AXIS_TVALID) |=> mst_exec_state==1'b0 );
  assert property ( (mst_exec_state==1'b0 &&  S_AXIS_TVALID) |=> mst_exec_state==1'b1 );
  // WRITE hold/exit
  assert property ( (mst_exec_state==1'b1 && !writes_done) |=> mst_exec_state==1'b1 );
  assert property ( (mst_exec_state==1'b1 &&  writes_done) |=> mst_exec_state==1'b0 );

  // TREADY consistency with state
  assert property ( S_AXIS_TREADY |-> mst_exec_state==1'b1 );
  assert property ( mst_exec_state==1'b0 |-> !S_AXIS_TREADY );

  // fifo_wren definition
  assert property ( fifo_wren == (S_AXIS_TVALID && S_AXIS_TREADY) );

  // Pointer always in range
  assert property ( write_pointer <= LAST );

  // Pointer progression
  // Increment only on fifo_wren, otherwise hold
  assert property ( (!fifo_wren) |=> write_pointer == $past(write_pointer) );
  // While not at LAST, fifo_wren increments by 1
  assert property ( (fifo_wren && $past(write_pointer) < LAST) |=> write_pointer == $past(write_pointer)+1 );

  // Termination rules
  // When a write occurs at LAST, writes_done must assert in that cycle
  assert property ( (fifo_wren && $past(write_pointer)==LAST) |-> writes_done );
  // writes_done only asserted due to TLAST or reaching LAST
  assert property ( writes_done |-> (S_AXIS_TLAST || (write_pointer==LAST)) );
  // writes_done should not assert outside WRITE state
  assert property ( (mst_exec_state!=1'b1) |-> !writes_done );
  // After writes_done, no further handshake next cycle (we go to IDLE)
  assert property ( (writes_done && mst_exec_state==1'b1) |=> (!S_AXIS_TREADY && !fifo_wren) );

  // Safe write: never write when pointer would be out-of-range
  assert property ( fifo_wren |-> write_pointer <= LAST );

  // Coverage
  cover property ( (mst_exec_state==1'b0 && S_AXIS_TVALID) |=> mst_exec_state==1'b1 );                 // enter WRITE
  cover property ( (mst_exec_state==1'b1, fifo_wren ##1 writes_done) );                                 // complete a burst
  cover property ( (mst_exec_state==1'b1 && fifo_wren && write_pointer==LAST) ##0 writes_done );        // done by count
  cover property ( (mst_exec_state==1'b1 && fifo_wren && S_AXIS_TLAST && write_pointer<LAST) ##0 writes_done ); // done by TLAST early
  // Exactly N handshakes then done (contiguous burst)
  sequence s_wren; fifo_wren; endsequence
  cover property ( (mst_exec_state==1'b1) ##1 (s_wren[*N]) ##0 writes_done );

endmodule

// Bind to DUT (connects to internal signals for deep checks)
bind daala_4x4_transpose_v1_0_S00_AXIS
  daala_4x4_transpose_sva #(.C_S_AXIS_TDATA_WIDTH(C_S_AXIS_TDATA_WIDTH),
                            .N(8)) // NUMBER_OF_INPUT_WORDS
  daala_4x4_transpose_sva_i (
    .clk(S_AXIS_ACLK),
    .rst_n(S_AXIS_ARESETN),
    .S_AXIS_TVALID(S_AXIS_TVALID),
    .S_AXIS_TLAST(S_AXIS_TLAST),
    .S_AXIS_TREADY(S_AXIS_TREADY),
    .mst_exec_state(mst_exec_state),
    .write_pointer(write_pointer),
    .writes_done(writes_done),
    .fifo_wren(fifo_wren)
  );