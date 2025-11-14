// SVA checker for axis_async_frame_fifo_64
// Bind this checker to the DUT instance (bind shown at end)

module axis_async_frame_fifo_64_sva #(
  parameter ADDR_WIDTH = 6
)(
  // DUT ports
  input  logic                input_clk,
  input  logic                input_rst,
  input  logic [63:0]         input_axis_tdata,
  input  logic [7:0]          input_axis_tkeep,
  input  logic                input_axis_tvalid,
  input  logic                input_axis_tlast,
  input  logic                input_axis_tuser,
  input  logic                input_axis_tready,

  input  logic                output_clk,
  input  logic                output_rst,
  input  logic [63:0]         output_axis_tdata,
  input  logic [7:0]          output_axis_tkeep,
  input  logic                output_axis_tvalid,
  input  logic                output_axis_tlast,
  input  logic                output_axis_tready,

  // Internal pointers (hierarchically connected via bind)
  input  logic [ADDR_WIDTH-1:0] write_ptr,
  input  logic [ADDR_WIDTH-1:0] read_ptr
);

  // --------------------------
  // Basic AXIS protocol checks
  // --------------------------

  // Input side: environment assumption (AXIS slave behavior expected)
  property a_input_hold_on_backpressure;
    @(posedge input_clk) disable iff (input_rst)
      input_axis_tvalid && !input_axis_tready |=> 
        input_axis_tvalid &&
        $stable(input_axis_tdata) &&
        $stable(input_axis_tkeep) &&
        $stable(input_axis_tlast) &&
        $stable(input_axis_tuser);
  endproperty
  assume property (a_input_hold_on_backpressure);

  // Output side: DUT must hold data stable when back-pressured
  property p_output_hold_on_backpressure;
    @(posedge output_clk) disable iff (output_rst)
      output_axis_tvalid && !output_axis_tready |=> 
        output_axis_tvalid &&
        $stable(output_axis_tdata) &&
        $stable(output_axis_tkeep) &&
        $stable(output_axis_tlast);
  endproperty
  assert property (p_output_hold_on_backpressure);

  // --------------------------
  // Reset behavior
  // --------------------------
  property p_input_reset;
    @(posedge input_clk)
      input_rst |=> (write_ptr == '0) && (input_axis_tready == 1'b1);
  endproperty
  assert property (p_input_reset);

  property p_output_reset;
    @(posedge output_clk)
      output_rst |=> (read_ptr == '0) && (output_axis_tvalid == 1'b0);
  endproperty
  assert property (p_output_reset);

  // --------------------------
  // Pointer movement semantics
  // --------------------------
  // Write pointer increments on handshake, otherwise stable
  property p_wrptr_incr_on_write;
    @(posedge input_clk) disable iff (input_rst)
      (input_axis_tvalid && input_axis_tready) |=> (write_ptr == $past(write_ptr) + 1);
  endproperty
  assert property (p_wrptr_incr_on_write);

  property p_wrptr_stable_without_write;
    @(posedge input_clk) disable iff (input_rst)
      !(input_axis_tvalid && input_axis_tready) |=> (write_ptr == $past(write_ptr));
  endproperty
  assert property (p_wrptr_stable_without_write);

  // Read pointer increments on output handshake; stalls otherwise
  property p_rdptr_incr_on_read;
    @(posedge output_clk) disable iff (output_rst)
      (output_axis_tvalid && output_axis_tready) |=> (read_ptr == $past(read_ptr) + 1);
  endproperty
  assert property (p_rdptr_incr_on_read);

  property p_rdptr_stable_on_backpressure;
    @(posedge output_clk) disable iff (output_rst)
      (output_axis_tvalid && !output_axis_tready) |=> (read_ptr == $past(read_ptr));
  endproperty
  assert property (p_rdptr_stable_on_backpressure);

  // --------------------------
  // Empty / Full safety
  // --------------------------
  // DUT advertises ready based on (read_ptr != write_ptr)
  property p_ready_matches_not_empty;
    @(posedge output_clk)
      output_axis_tready == (read_ptr != write_ptr);
  endproperty
  assert property (p_ready_matches_not_empty);

  // No read/prime from empty (no output valid when empty)
  property p_no_output_valid_when_empty;
    @(posedge output_clk) disable iff (output_rst)
      (read_ptr == write_ptr) |-> !output_axis_tvalid;
  endproperty
  assert property (p_no_output_valid_when_empty);

  // Read pointer must not change when empty
  property p_no_rdptr_change_when_empty;
    @(posedge output_clk) disable iff (output_rst)
      (read_ptr == write_ptr) |=> (read_ptr == $past(read_ptr));
  endproperty
  assert property (p_no_rdptr_change_when_empty);

  // No write into full (one-slot-empty full definition)
  property p_no_write_when_full;
    @(posedge input_clk) disable iff (input_rst)
      ((write_ptr + 1'b1) == read_ptr) |-> !(input_axis_tvalid && input_axis_tready);
  endproperty
  assert property (p_no_write_when_full);

  // --------------------------
  // End-to-end ordering/data integrity using a simple scoreboard
  // --------------------------
  typedef struct packed {
    logic [63:0] data;
    logic [7:0]  keep;
    logic        last;
    logic        user;
  } beat_t;

  beat_t q[$];

  // Push on input handshake
  always @(posedge input_clk) begin
    if (!input_rst && input_axis_tvalid && input_axis_tready) begin
      q.push_back('{input_axis_tdata, input_axis_tkeep, input_axis_tlast, input_axis_tuser});
    end
  end

  // Pop and compare on output handshake
  always @(posedge output_clk) begin
    if (!output_rst && output_axis_tvalid && output_axis_tready) begin
      assert (q.size() > 0)
        else $error("Underflow: output popped with empty model queue");
      if (q.size() > 0) begin
        beat_t exp = q.pop_front();
        assert (output_axis_tdata === exp.data)
          else $error("Data mismatch: exp=%0h got=%0h", exp.data, output_axis_tdata);
        assert (output_axis_tkeep === exp.keep)
          else $error("Keep mismatch: exp=%0h got=%0h", exp.keep, output_axis_tkeep);
        assert (output_axis_tlast === exp.last)
          else $error("Last mismatch: exp=%0b got=%0b", exp.last, output_axis_tlast);
      end
    end
  end

  // When model queue empty, DUT should not claim valid
  property p_no_valid_when_model_empty;
    @(posedge output_clk) disable iff (output_rst)
      (q.size() == 0) |-> !output_axis_tvalid;
  endproperty
  assert property (p_no_valid_when_model_empty);

  // --------------------------
  // Concise functional coverage
  // --------------------------
  // At least one push and one pop
  cover property (@(posedge input_clk)  disable iff (input_rst)  input_axis_tvalid && input_axis_tready);
  cover property (@(posedge output_clk) disable iff (output_rst) output_axis_tvalid && output_axis_tready);

  // Transfer of TLAST on both sides
  cover property (@(posedge input_clk)  disable iff (input_rst)  input_axis_tvalid && input_axis_tready && input_axis_tlast);
  cover property (@(posedge output_clk) disable iff (output_rst) output_axis_tvalid && output_axis_tready && output_axis_tlast);

  // Backpressure observed on output
  cover property (@(posedge output_clk) disable iff (output_rst)
                  output_axis_tvalid && !output_axis_tready ##1
                  output_axis_tvalid && !output_axis_tready ##1
                  output_axis_tvalid && output_axis_tready);

endmodule

// Bind into the DUT (connect internals by name)
bind axis_async_frame_fifo_64 axis_async_frame_fifo_64_sva #(.ADDR_WIDTH(6)) sva_i (
  // DUT ports
  .input_clk(input_clk),
  .input_rst(input_rst),
  .input_axis_tdata(input_axis_tdata),
  .input_axis_tkeep(input_axis_tkeep),
  .input_axis_tvalid(input_axis_tvalid),
  .input_axis_tlast(input_axis_tlast),
  .input_axis_tuser(input_axis_tuser),
  .input_axis_tready(input_axis_tready),

  .output_clk(output_clk),
  .output_rst(output_rst),
  .output_axis_tdata(output_axis_tdata),
  .output_axis_tkeep(output_axis_tkeep),
  .output_axis_tvalid(output_axis_tvalid),
  .output_axis_tlast(output_axis_tlast),
  .output_axis_tready(output_axis_tready),

  // Internals
  .write_ptr(write_ptr),
  .read_ptr(read_ptr)
);