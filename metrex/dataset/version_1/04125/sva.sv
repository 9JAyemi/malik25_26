// SVA checker for FIFO_WxD. Bind this to your DUT.
module FIFO_WxD_SVA #(parameter int U_FIFO_WIDTH = 24,
                      parameter int U_FIFO_SQ_DEPTH = 10);
  // Assumes it is bound into the scope of FIFO_WxD, so DUT internals are visible.
  localparam int PTRW  = U_FIFO_SQ_DEPTH;
  localparam int DEPTH = 1 << U_FIFO_SQ_DEPTH;

  // Basic invariants on flags (sample on any side’s event)
  assert property (@(posedge wr_en or posedge rd_en)
                   empty_flg == (wr_ptr == rd_ptr));

  assert property (@(posedge wr_en or posedge rd_en)
                   full_flg  == ((wr_ptr + {{PTRW-1{1'b0}},1'b1}) == rd_ptr));

  assert property (@(posedge wr_en or posedge rd_en)
                   !(full_flg && empty_flg));

  // Reset behavior (asynchronous active-low)
  assert property (@(negedge rst) ##0
                   (wr_ptr == '0 && rd_ptr == '0 && empty_flg && !full_flg && dataOut == '0));

  // Write side pointer behavior
  assert property (@(posedge wr_en) disable iff (!rst)
                   !full_flg |-> wr_ptr == $past(wr_ptr) + 1);

  assert property (@(posedge wr_en) disable iff (!rst)
                   full_flg |-> $stable(wr_ptr));

  // Read side pointer behavior
  assert property (@(posedge rd_en) disable iff (!rst)
                   !empty_flg |-> rd_ptr == $past(rd_ptr) + 1);

  assert property (@(posedge rd_en) disable iff (!rst)
                   empty_flg |-> $stable(rd_ptr));

  // Cross-side stability (no unintended pointer movement)
  assert property (@(posedge wr_en) disable iff (!rst) $stable(rd_ptr));
  assert property (@(posedge rd_en) disable iff (!rst) $stable(wr_ptr));

  // DataOut mapping and empty behavior
  assert property (@(posedge wr_en or posedge rd_en) disable iff (!rst)
                   empty_flg |-> dataOut == '0);

  assert property (@(posedge wr_en or posedge rd_en) disable iff (!rst)
                   !empty_flg |-> dataOut == fifo[rd_ptr]);

  // Lightweight reference model (scoreboard) to check data integrity on reads
  reg [U_FIFO_WIDTH-1:0] ref_mem [0:DEPTH-1];
  reg [PTRW-1:0] ref_wr_ptr, ref_rd_ptr;

  // Reference write pointer mirrors DUT write semantics
  always @(negedge rst or posedge wr_en) begin
    if (!rst) begin
      ref_wr_ptr <= '0;
    end else if (!full_flg) begin
      ref_mem[ref_wr_ptr] <= dataIn;
      ref_wr_ptr <= ref_wr_ptr + 1'b1;
    end
  end

  // Reference read pointer mirrors DUT read semantics
  always @(negedge rst or posedge rd_en) begin
    if (!rst) begin
      ref_rd_ptr <= '0;
    end else if (!empty_flg) begin
      ref_rd_ptr <= ref_rd_ptr + 1'b1;
    end
  end

  // DUT pointers should match the reference model on their respective clocks
  assert property (@(posedge wr_en) disable iff (!rst) wr_ptr == ref_wr_ptr);
  assert property (@(posedge rd_en) disable iff (!rst) rd_ptr == ref_rd_ptr);

  // Data integrity: when a read is accepted, it must return the enqueued data
  assert property (@(posedge rd_en) disable iff (!rst)
                   !empty_flg |-> dataOut == ref_mem[ref_rd_ptr]);

  // Corner/functional coverage
  cover property (@(negedge rst) ##1 empty_flg && !full_flg && wr_ptr=='0 && rd_ptr=='0);
  cover property (@(posedge wr_en) disable iff (!rst) !full_flg);
  cover property (@(posedge rd_en) disable iff (!rst) !empty_flg);
  cover property (@(posedge wr_en) disable iff (!rst) full_flg);      // reached full
  cover property (@(posedge rd_en) disable iff (!rst) empty_flg);     // reached empty
  cover property (@(posedge wr_en) disable iff (!rst)
                  !full_flg && (wr_ptr == {PTRW{1'b1}}) ##1 (wr_ptr == '0)); // write wrap
  cover property (@(posedge rd_en) disable iff (!rst)
                  !empty_flg && (rd_ptr == {PTRW{1'b1}}) ##1 (rd_ptr == '0)); // read wrap
endmodule

// Bind into all FIFO_WxD instances
bind FIFO_WxD FIFO_WxD_SVA #(.U_FIFO_WIDTH(U_FIFO_WIDTH),
                             .U_FIFO_SQ_DEPTH(U_FIFO_SQ_DEPTH)) u_FIFO_WxD_SVA();