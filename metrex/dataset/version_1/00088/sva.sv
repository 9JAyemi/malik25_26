// SVA checker for FIFO_WxD
// Bind this to the DUT; focuses on key correctness, safety, and compact coverage.

module fifo_wxd_sva #(
  parameter int U_FIFO_WIDTH   = 24,
  parameter int U_FIFO_SQ_DEPTH = 10
)(
  input  logic                         rst,
  input  logic [U_FIFO_WIDTH-1:0]      dataIn,
  input  logic                         wr_en,
  input  logic                         rd_en,
  input  logic [U_FIFO_WIDTH-1:0]      dataOut,
  input  logic                         full_flg,
  input  logic                         empty_flg,

  // internal DUT signals
  input  logic [U_FIFO_SQ_DEPTH-1:0]   wr_ptr,
  input  logic [U_FIFO_SQ_DEPTH-1:0]   rd_ptr,
  // unpacked array port to peek memory
  input  logic [U_FIFO_WIDTH-1:0]      fifo [ (1<<U_FIFO_SQ_DEPTH) - 1 : 0 ]
);

  // Flag correctness and mutual exclusion (checked on any write/read activity)
  property p_flags_correct;
    @(posedge wr_en or posedge rd_en) disable iff (!rst)
      ( empty_flg == (wr_ptr == rd_ptr) )
      && ( full_flg  == ((wr_ptr + {{U_FIFO_SQ_DEPTH-1{1'b0}},1'b1}) == rd_ptr) )
      && !(empty_flg && full_flg);
  endproperty
  assert property (p_flags_correct);

  // After async reset asserted, FIFO returns to known empty state
  property p_reset_state;
    @(negedge rst) 1 |=> (wr_ptr == '0 && rd_ptr == '0 && empty_flg && !full_flg && dataOut == '0);
  endproperty
  assert property (p_reset_state);

  // Data output matches muxing: zero when empty, otherwise fifo[rd_ptr]
  property p_dataout_mux;
    @(posedge wr_en or posedge rd_en) disable iff (!rst)
      ( empty_flg -> (dataOut == '0) )
      and ( (!empty_flg) -> (dataOut == fifo[rd_ptr]) );
  endproperty
  assert property (p_dataout_mux);

  // Write pointer behavior on wr_en pulses
  // - If full, wr_ptr must not advance
  property p_wrptr_stable_on_full;
    @(posedge wr_en) disable iff (!rst)
      full_flg |-> ##1 (wr_ptr == $past(wr_ptr));
  endproperty
  assert property (p_wrptr_stable_on_full);

  // - If not full, wr_ptr advances by +1 (wraps naturally)
  property p_wrptr_inc_on_accept;
    @(posedge wr_en) disable iff (!rst)
      (!full_flg) |-> ##1 (wr_ptr == $past(wr_ptr) + 1'b1);
  endproperty
  assert property (p_wrptr_inc_on_accept);

  // Read pointer behavior on rd_en pulses
  // - If empty, rd_ptr must not advance
  property p_rdptr_stable_on_empty;
    @(posedge rd_en) disable iff (!rst)
      empty_flg |-> ##1 (rd_ptr == $past(rd_ptr));
  endproperty
  assert property (p_rdptr_stable_on_empty);

  // - If not empty, rd_ptr advances by +1 (wraps naturally)
  property p_rdptr_inc_on_accept;
    @(posedge rd_en) disable iff (!rst)
      (!empty_flg) |-> ##1 (rd_ptr == $past(rd_ptr) + 1'b1);
  endproperty
  assert property (p_rdptr_inc_on_accept);

  // Data integrity: any accepted write must be returned unchanged
  // when that exact index is read later.
  property p_data_order;
    automatic logic [U_FIFO_SQ_DEPTH-1:0] idx;
    automatic logic [U_FIFO_WIDTH-1:0]    val;
    @(posedge wr_en) disable iff (!rst)
      (!full_flg, idx = wr_ptr, val = dataIn)
      |-> ##[1:$] @(posedge rd_en)
            (rd_ptr == idx && !empty_flg) ##0 (dataOut == val);
  endproperty
  assert property (p_data_order);

  // Coverage: observe corner conditions and wrap-around
  cover property (@(posedge wr_en) disable iff (!rst) !full_flg ##1 full_flg);         // reach full
  cover property (@(posedge rd_en) disable iff (!rst) !empty_flg ##1 empty_flg);       // reach empty
  cover property (@(posedge wr_en) disable iff (!rst) full_flg);                       // write attempted while full
  cover property (@(posedge rd_en) disable iff (!rst) empty_flg);                      // read attempted while empty
  cover property (@(posedge wr_en) disable iff (!rst)
                  $past(wr_ptr) == {U_FIFO_SQ_DEPTH{1'b1}} && wr_ptr == '0);          // wr_ptr wrap
  cover property (p_data_order);                                                       // write->read return

endmodule

// Bind into the DUT (tooling can also inline these asserts inside the RTL if preferred)
bind FIFO_WxD fifo_wxd_sva #(
  .U_FIFO_WIDTH(U_FIFO_WIDTH),
  .U_FIFO_SQ_DEPTH(U_FIFO_SQ_DEPTH)
) fifo_wxd_sva_i (
  .rst(rst),
  .dataIn(dataIn),
  .wr_en(wr_en),
  .rd_en(rd_en),
  .dataOut(dataOut),
  .full_flg(full_flg),
  .empty_flg(empty_flg),
  .wr_ptr(wr_ptr),
  .rd_ptr(rd_ptr),
  .fifo(fifo)
);