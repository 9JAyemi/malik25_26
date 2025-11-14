// SVA for mutex_buffer
// Bind this module to the DUT: bind mutex_buffer mutex_buffer_sva #(.C_BUFF_NUM(C_BUFF_NUM)) i_mutex_buffer_sva();

module mutex_buffer_sva #(parameter int C_BUFF_NUM = 4) ();

  // Elaboration-time sanity
  initial begin
    if (C_BUFF_NUM < 1) $fatal(1, "C_BUFF_NUM must be >= 1");
  end

  // Local constants
  localparam logic [C_BUFF_NUM-1:0] LSB_ONE = {{C_BUFF_NUM-1{1'b0}}, 1'b1};

  // Helper: compute expected next write bitmap (pick lowest 0 in mask; if all 1's => 0)
  function automatic logic [C_BUFF_NUM-1:0] wbmp_next_from_mask(input logic [C_BUFF_NUM-1:0] m);
    logic [C_BUFF_NUM-1:0] res;
    res = '0;
    for (int k = 0; k < C_BUFF_NUM; k++) begin
      if ((m[k] == 1'b0) && ((k == 0) ? 1'b1 : (&m[k-1:0]))) begin
        res[k] = 1'b1;
        break;
      end
    end
    return res;
  endfunction

  // Default clocking and reset guard
  default clocking cb @(posedge clk); endclocking
  default disable iff (!resetn);

  // 1) Reset behavior
  assert property (!resetn |-> (r0_bmp == '0 && r1_bmp == '0 && w_bmp == '0 && last_bmp == LSB_ONE));

  // 2) No X/Z on key regs/outs after reset
  assert property (!$isunknown({w_sof, r0_sof, r1_sof, wr_done}));
  assert property (!$isunknown({w_bmp, r0_bmp, r1_bmp, last_bmp}));

  // 3) Basic correctness
  assert property (wr_done == w_sof);

  // Onehot-or-zero encodings
  assert property ($onehot0(w_bmp));
  assert property ($onehot0(last_bmp));
  assert property ($onehot0(r0_bmp));
  assert property ($onehot0(r1_bmp));

  // 4) last_bmp tracking of last write
  assert property ( w_sof |-> (last_bmp == $past(w_bmp)) );
  assert property (!w_sof |-> $stable(last_bmp));

  // 5) Reader sampling semantics
  assert property ( r0_sof |-> (r0_bmp == ($past(w_sof) ? $past(w_bmp) : $past(last_bmp))) );
  assert property ( r1_sof |-> (r1_bmp == ($past(w_sof) ? $past(w_bmp) : $past(last_bmp))) );
  assert property (!r0_sof |-> $stable(r0_bmp));
  assert property (!r1_sof |-> $stable(r1_bmp));

  // Simultaneous readers get same snapshot (from w_bmp if w_sof else last_bmp)
  assert property ( (r0_sof && r1_sof) |-> (r0_bmp == r1_bmp) );
  assert property ( (r0_sof && r1_sof) |-> (r0_bmp == ($past(w_sof) ? $past(w_bmp) : $past(last_bmp))) );

  // 6) Writer next-state function and stability
  assert property ( w_sof |-> (w_bmp == wbmp_next_from_mask($past(w_bmp | r0_bmp | r1_bmp))) );
  assert property (!w_sof |-> $stable(w_bmp));

  // 7) Functional coverage (concise but meaningful)
  // Each one-hot position selected at least once on a write
  generate
    for (genvar i = 0; i < C_BUFF_NUM; i++) begin : C_WBMP_BITS
      cover property ( w_sof && (w_bmp == (logic'(1) << i)) );
    end
  endgenerate
  // Cover default path (all ones in mask -> w_bmp becomes zero)
  cover property ( w_sof && ( ( $past(w_bmp | r0_bmp | r1_bmp) == {C_BUFF_NUM{1'b1}} ) && (w_bmp == '0) ) );
  // Concurrent access scenarios
  cover property ( r0_sof && r1_sof &&  w_sof );
  cover property ( r0_sof && r1_sof && !w_sof );

endmodule