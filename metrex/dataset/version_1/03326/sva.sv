// SVA checker for fifo
// Bind this module to the DUT instance: bind fifo fifo_sva #(DEPTH,WIDTH) fifo_sva_i(.*);

module fifo_sva #(parameter DEPTH=16, WIDTH=32)
(
  input clk, rst, en, we, re,
  input [1:0] mode,
  input [WIDTH-1:0] din,
  input [WIDTH-1:0] dout,
  input [1:0] status,
  input full, empty,

  // internal DUT signals (resolved in target scope by bind)
  input [4:0] wp, rp,
  input       empty_reg,
  input [WIDTH-1:0] mem [0:DEPTH-1]
);

  default clocking cb @(posedge clk); endclocking
  // Use disable iff(rst) for steady-state checks; separate reset checks below
  default disable iff (rst);

  // Convenience handshakes
  wire wr_acc = en && we && !full;
  wire rd_acc = en && re && !empty;

  // Basic invariants
  assert property ( !(full && empty) );
  assert property ( full  == ((wp == rp) && !empty_reg) );
  assert property ( empty == ((wp == rp) &&  empty_reg) );

  // Pointer range (catch out-of-bounds indexing)
  assert property ( wp < DEPTH );
  assert property ( rp < DEPTH );

  // Pointer updates only on accepted ops
  assert property ( wr_acc |-> ##1 wp == $past(wp) + 1 );
  assert property ( !wr_acc |-> ##1 wp == $past(wp) );

  assert property ( rd_acc |-> ##1 rp == $past(rp) + 1 );
  assert property ( !rd_acc |-> ##1 rp == $past(rp) );

  // When en is low, pointers hold
  assert property ( !en |-> ##1 (wp == $past(wp) && rp == $past(rp)) );

  // No read pointer advance when empty; no write pointer advance when full
  assert property ( full  |-> ##1 wp == $past(wp) );
  assert property ( empty |-> ##1 rp == $past(rp) );

  // Status encodes previous cycle full/empty
  assert property ( status == ($past(full)  ? 2'b10
                             : $past(empty) ? 2'b00
                                            : 2'b01) );

  // Empty deasserts after a successful write when previously empty
  assert property ( $past(empty) && $past(wr_acc) |-> !empty );

  // Full deasserts after a successful read when previously full
  assert property ( $past(full) && $past(rd_acc) |-> !full );

  // dout updates only on accepted read; otherwise holds value
  assert property ( !rd_acc |-> ##1 dout == $past(dout) );

  // dout data transform correctness (next-cycle dout from prior-cycle mem/rp)
  assert property ( rd_acc && mode==2'b00 |-> ##1
                    dout == {16'h0000, $past(mem[$past(rp)][15:0])} );

  assert property ( rd_acc && mode==2'b01 |-> ##1
                    dout == {{14{1'b0}}, $past(mem[$past(rp)][17:0]), 2'b00} );

  assert property ( rd_acc && mode==2'b10 |-> ##1
                    dout == $past(mem[$past(rp)]) );

  assert property ( rd_acc && mode==2'b11 |-> ##1
                    dout == '0 );

  // Write data correctness into memory
  assert property ( wr_acc |-> ##1 mem[$past(wp)] == $past(din) );

  // Reset behavior (checked explicitly without disable iff)
  // After a cycle with rst high, next cycle state is initialized
  assert property (@(posedge clk)
                   rst |-> ##1 (wp==0 && rp==0 && empty_reg==1'b1
                                && empty==1'b1 && full==1'b0
                                && status==2'b00 && dout=='0) );

  // Coverage
  cover property ( $fell(rst) );                      // exit reset
  cover property ( wr_acc );                          // write accepted
  cover property ( rd_acc );                          // read accepted
  cover property ( wr_acc && rd_acc );                // simultaneous read & write
  cover property ( full );                            // full seen
  cover property ( empty );                           // empty seen
  cover property ( rd_acc && mode==2'b00 );
  cover property ( rd_acc && mode==2'b01 );
  cover property ( rd_acc && mode==2'b10 );
  cover property ( rd_acc && mode==2'b11 );
  cover property ( (empty, wr_acc, !empty, rd_acc, empty) ); // empty->write->read->empty flow

endmodule

// Example bind (place in a testbench or package):
// bind fifo fifo_sva #(.DEPTH(DEPTH), .WIDTH(WIDTH)) fifo_sva_i (.*);