// SVA checker for fifo_async
// Quality-focused, concise assertions and covers

module fifo_async_sva #(parameter int DW=104, DEPTH=16, AW=5)
(
  input  logic                    wr_en,
  input  logic                    rd_en,
  input  logic                    full,
  input  logic                    prog_full,
  input  logic                    empty,
  input  logic                    valid,
  input  logic [DW-1:0]           din,
  input  logic [DW-1:0]           dout,
  input  logic [AW-1:0]           wr_ptr,
  input  logic [AW-1:0]           rd_ptr,
  input  logic [AW-1:0]           fifo_count
);

  // Helper: modulo increment expectation for pointers
  function automatic logic [AW-1:0] inc_mod(input logic [AW-1:0] v);
    return (v == DEPTH-1) ? '0 : (v + 1'b1);
  endfunction

  // Basic flag consistency (redundant with assigns, but catches X/unknowns)
  assert property (@(posedge wr_en)  valid == !empty);
  assert property (@(posedge rd_en)  valid == !empty);
  assert property (@(posedge wr_en)  full  |-> prog_full);
  assert property (@(posedge rd_en)  full  |-> prog_full);
  assert property (@(posedge wr_en) !(full && empty));
  assert property (@(posedge rd_en) !(full && empty));

  // No X on key state at activity edges
  assert property (@(posedge wr_en) !$isunknown({full,prog_full,empty,valid,wr_ptr,rd_ptr,fifo_count}));
  assert property (@(posedge rd_en) !$isunknown({full,prog_full,empty,valid,wr_ptr,rd_ptr,fifo_count}));

  // Bounds: pointers must not index outside the FIFO array
  assert property (@(posedge wr_en) wr_ptr < DEPTH);
  assert property (@(posedge rd_en) rd_ptr < DEPTH);

  // Count must remain within 0..DEPTH (no wrap/underflow)
  assert property (@(posedge wr_en) fifo_count <= DEPTH);
  assert property (@(posedge rd_en) fifo_count <= DEPTH);

  // Write side behavior
  // - When full, write pointer must not advance
  // - When not full, write pointer must advance with wrap at DEPTH
  assert property (@(posedge wr_en)  full  |=> $stable(wr_ptr));
  assert property (@(posedge wr_en) !full  |=> wr_ptr == inc_mod($past(wr_ptr,1,wr_en)));
  // Data driven on write must be known
  assert property (@(posedge wr_en) !full  |-> !$isunknown(din));

  // Read side behavior
  // - When empty, read pointer must not advance
  // - When not empty, read pointer must advance with wrap at DEPTH
  assert property (@(posedge rd_en)  empty |=> $stable(rd_ptr));
  assert property (@(posedge rd_en) !empty |=> rd_ptr == inc_mod($past(rd_ptr,1,rd_en)));
  // When reading valid data, dout must be known
  assert property (@(posedge rd_en) !empty |-> !$isunknown(dout));

  // dout should not change unless rd_ptr changes (combinational read-from-pointer)
  assert property (@(posedge wr_en)  $stable(rd_ptr) |-> $stable(dout));
  assert property (@(posedge rd_en)  $stable(rd_ptr) |-> $stable(dout));

  // Coverage: exercise key states and edges
  cover property (@(posedge wr_en) !full  ##1 full);                  // fill to full
  cover property (@(posedge rd_en) !empty ##1 empty);                 // drain to empty
  cover property (@(posedge wr_en) prog_full);                        // near-full threshold
  cover property (@(posedge rd_en) empty);                            // read-at-empty attempt
  cover property (@(posedge wr_en) full);                             // write-at-full attempt
  cover property (@(posedge wr_en) ($past(wr_ptr,1,wr_en)==DEPTH-1) && !full
                               |=> (wr_ptr=='0));                     // wrap on write
  cover property (@(posedge rd_en) ($past(rd_ptr,1,rd_en)==DEPTH-1) && !empty
                               |=> (rd_ptr=='0));                     // wrap on read

endmodule

// Bind to DUT
bind fifo_async fifo_async_sva #(.DW(DW), .DEPTH(DEPTH), .AW(5)) u_fifo_async_sva (
  .wr_en(wr_en),
  .rd_en(rd_en),
  .full(full),
  .prog_full(prog_full),
  .empty(empty),
  .valid(valid),
  .din(din),
  .dout(dout),
  .wr_ptr(wr_ptr),
  .rd_ptr(rd_ptr),
  .fifo_count(fifo_count)
);