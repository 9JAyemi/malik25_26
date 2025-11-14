// SVA for fifo_fwft_adapter
// Bind this checker to the DUT. Concise, high-quality checks and functional coverage.
module fifo_fwft_adapter_sva #(parameter DATA_WIDTH = 0) (
  input  logic                  clk,
  input  logic                  rst,

  // DUT ports
  input  logic                  rd_en,
  input  logic                  fifo_empty,
  input  logic                  fifo_rd_en,
  input  logic [DATA_WIDTH-1:0] fifo_dout,
  input  logic [DATA_WIDTH-1:0] dout,
  input  logic                  empty,
  input  logic                  valid,

  // DUT internals
  input  logic                  fifo_valid,
  input  logic                  middle_valid,
  input  logic                  dout_valid,
  input  logic [DATA_WIDTH-1:0] middle_dout,
  input  logic [DATA_WIDTH-1:0] last_dout,
  input  logic                  next_dout
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Combinational signal definitions must hold
  ap_empty_def:      assert property (empty == !dout_valid);
  ap_valid_def:      assert property (valid == dout_valid);
  ap_next_dout_def:  assert property (next_dout == (rd_en || !dout_valid));
  ap_fifo_rd_en_def: assert property (fifo_rd_en == ((!fifo_empty) && !(middle_valid && dout_valid && fifo_valid)));

  // Reset state (synchronous)
  ap_reset_regs: assert property (
    rst |=> (!fifo_valid && !middle_valid && !dout_valid &&
             middle_dout == '0 && dout == '0 && last_dout == '0)
  );

  // fifo_valid set/clear protocol
  ap_fifo_valid_set:  assert property (fifo_rd_en |=> fifo_valid);
  ap_fifo_valid_clr:  assert property ((!fifo_rd_en && (!middle_valid || next_dout)) |=> !fifo_valid);
  ap_fifo_valid_hold: assert property ((!fifo_rd_en && (middle_valid && !next_dout)) |=> fifo_valid == $past(fifo_valid));

  // Middle stage update protocol
  ap_mid_update: assert property (
    (middle_valid == next_dout) |=> (middle_valid == $past(fifo_valid) && middle_dout == $past(fifo_dout))
  );
  ap_mid_hold: assert property (
    (middle_valid != next_dout) |=> (middle_valid == $past(middle_valid) && middle_dout == $past(middle_dout))
  );

  // dout_valid update protocol
  ap_dv_update: assert property (
    next_dout |=> dout_valid == ($past(fifo_valid) || $past(middle_valid))
  );
  ap_dv_hold: assert property (
    !next_dout |=> dout_valid == $past(dout_valid)
  );

  // Data muxing and last_dout updates
  ap_dout_from_fifo: assert property (
    next_dout && $past(fifo_valid) |=> (dout == $past(fifo_dout) && last_dout == $past(fifo_dout))
  );
  ap_dout_from_mid: assert property (
    next_dout && !$past(fifo_valid) && $past(middle_valid) |=> (dout == $past(middle_dout) && last_dout == $past(middle_dout))
  );
  ap_no_new_data: assert property (
    next_dout && !$past(fifo_valid) && !$past(middle_valid) |=> (!dout_valid && last_dout == $past(last_dout) && dout == last_dout)
  );

  // Holding behavior when not advancing
  ap_last_hold: assert property (!next_dout |=> last_dout == $past(last_dout));
  ap_hold_when_valid_and_not_read: assert property (dout_valid && !rd_en |=> dout == $past(dout) && last_dout == $past(last_dout));

  // Safety: no read when empty (redundant to equivalence but explicit)
  ap_no_read_when_empty: assert property (fifo_empty |-> !fifo_rd_en);

  // Functional coverage

  // FWFT: When output is empty and FIFO has data, a word eventually appears on dout without needing rd_en
  cover_fwft_first_word: cover property (
    !dout_valid && !fifo_empty ##1
    fifo_rd_en ##1
    !dout_valid ##1
    dout_valid && (dout == $past(fifo_dout,1))
  );

  // Backpressure/triple-valid gating: when all stages valid and FIFO not empty, no read issues
  cover_triple_valid_gate: cover property (
    middle_valid && dout_valid && fifo_valid && !fifo_empty && !fifo_rd_en
  );

  // Steady streaming: while continuously reading and FIFO not empty, output stays valid
  cover_streaming: cover property (
    dout_valid && !fifo_empty ##1
    (rd_en, 1) [*3] ##1
    (dout_valid)
  );
endmodule

bind fifo_fwft_adapter fifo_fwft_adapter_sva #(.DATA_WIDTH(DATA_WIDTH)) fifo_fwft_adapter_sva_b (.*);