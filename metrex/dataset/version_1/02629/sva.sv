// SVA checker for fifo. Bind this to the DUT.
// Focus: reset, flags, counters, pointers, data ordering, overflow/underflow, wrap, and coverage.

module fifo_sva #(
  parameter int DW      = 30,
  parameter int ADDR_W  = 5,
  parameter int DEPTH   = 32
)(
  input  logic                 clock,
  input  logic                 aclr,      // active low
  input  logic [DW-1:0]        data,
  input  logic                 rdreq,
  input  logic                 wrreq,
  input  logic                 empty,
  input  logic                 full,
  input  logic [DW-1:0]        q,
  input  logic [ADDR_W-1:0]    usedw,

  // Internal pointers (for stronger checks and coverage)
  input  logic [ADDR_W-1:0]    write_ptr_reg,
  input  logic [ADDR_W-1:0]    read_ptr_reg
);

  localparam int MAX = DEPTH-1;

  default clocking cb @(posedge clock); endclocking
  default disable iff (!aclr);

  // Basic sanity
  assert property (usedw <= MAX);
  assert property (!(full && empty));

  // Reset state (synchronous in this RTL)
  assert property (@(posedge clock) !aclr |-> (empty && !full && (usedw=='0) && (q=='0)
                                              && (write_ptr_reg=='0) && (read_ptr_reg=='0)));

  // Flag consistency with count
  assert property (empty == (usedw=='0));
  assert property (full  == (usedw==MAX));

  // Accept conditions
  sequence acc_wr; wrreq && !full; endsequence
  sequence acc_rd; rdreq && !empty; endsequence

  // usedw accounting
  assert property (acc_wr  && !acc_rd |=> usedw == $past(usedw)+1);
  assert property (acc_rd  && !acc_wr |=> usedw == $past(usedw)-1);
  assert property (acc_wr  &&  acc_rd |=> usedw == $past(usedw)); // simultaneous R/W
  assert property (wrreq &&  full     |=> usedw == $past(usedw));
  assert property (rdreq &&  empty    |=> usedw == $past(usedw));

  // Pointer movement and blocking
  function automatic [ADDR_W-1:0] inc(input [ADDR_W-1:0] a);
    inc = (a==MAX) ? '0 : a+1;
  endfunction

  assert property (acc_wr |=> write_ptr_reg == inc($past(write_ptr_reg)));
  assert property (acc_rd |=> read_ptr_reg  == inc($past(read_ptr_reg)));
  assert property (wrreq && full  |=> $stable(write_ptr_reg));
  assert property (rdreq && empty |=> $stable(read_ptr_reg) && $stable(q));

  // Count matches pointer distance (mod DEPTH)
  assert property (usedw == (write_ptr_reg - read_ptr_reg));

  // Simple data-ordering scoreboard (model against accepted R/W)
  logic [DW-1:0] model_mem [0:DEPTH-1];
  logic [ADDR_W-1:0] mwptr, mrptr;

  always_ff @(posedge clock) begin
    if (!aclr) begin
      mwptr <= '0; mrptr <= '0;
    end else begin
      if (wrreq && !full) begin
        model_mem[mwptr] <= data;
        mwptr <= inc(mwptr);
      end
      if (rdreq && !empty) begin
        assert (q == model_mem[mrptr])
          else $error("FIFO data ordering mismatch: q=%0h exp=%0h @%0t", q, model_mem[mrptr], $time);
        mrptr <= inc(mrptr);
      end
    end
  end

  // Coverage
  cover property (acc_wr);
  cover property (acc_rd);
  cover property (acc_wr && acc_rd);                       // simultaneous R/W
  cover property (acc_wr ##1 write_ptr_reg=='0);           // write wrap-around
  cover property (acc_rd ##1 read_ptr_reg=='0);            // read wrap-around
  cover property (empty ##1 acc_wr ##[1:$] full);          // reach full
  cover property (full  ##1 acc_rd ##[1:$] empty);         // drain to empty

endmodule

// Bind example (place in a suitable package or a TB file):
// bind fifo fifo_sva #(.DW(30), .ADDR_W(5), .DEPTH(32)) fifo_sva_i (.*,
//   .write_ptr_reg(write_ptr_reg), .read_ptr_reg(read_ptr_reg));