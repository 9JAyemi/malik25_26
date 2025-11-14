// Bindable SVA for dma_access. Focused on protocol, handshakes, and outputs.
// Bind example: bind dma_access dma_access_sva u_dma_access_sva (.*);

module dma_access_sva
(
  input  logic        clk,
  input  logic        rst_n,

  input  logic        dma_req,
  input  logic [21:0] dma_addr,
  input  logic        dma_rnw,
  input  logic [7:0]  dma_wd,
  input  logic [7:0]  dma_rd,
  input  logic        dma_busynready,
  input  logic        dma_ack,
  input  logic        dma_end,

  input  logic        mem_dma_bus,
  input  logic [21:0] mem_dma_addr,
  input  logic [7:0]  mem_dma_wd,
  input  logic [7:0]  mem_dma_rd,
  input  logic        mem_dma_rnw,
  input  logic        mem_dma_oe,
  input  logic        mem_dma_we,

  input  logic        busrq_n,
  input  logic        busak_n
);

  // Reset values (asynchronously asserted, sampled on posedge)
  assert property (@(posedge clk) !rst_n |-> (busrq_n && mem_dma_oe && mem_dma_we &&
                                              !dma_busynready && !dma_ack && !dma_end &&
                                              !mem_dma_bus));

  // Bus must not be driven until bus granted
  assert property (@(posedge clk) disable iff (!rst_n) busak_n |-> (!mem_dma_bus && mem_dma_oe));

  // START phase: bus request asserted and latches captured
  assert property (@(posedge clk) disable iff (!rst_n)
                   $fell(busrq_n) |-> (dma_ack && dma_busynready &&
                                       mem_dma_addr==dma_addr &&
                                       mem_dma_wd  ==dma_wd   &&
                                       mem_dma_rnw ==dma_rnw));

  // Bus drive begins only after grant was low in the previous cycle
  assert property (@(posedge clk) disable iff (!rst_n)
                   $rose(mem_dma_bus) |-> !$past(busak_n));

  // While bus is driven, direction and OE must agree
  assert property (@(posedge clk) disable iff (!rst_n)
                   mem_dma_bus |-> (mem_dma_oe == ~mem_dma_rnw));

  // When bus is not driven, OE must be deasserted (high)
  assert property (@(posedge clk) disable iff (!rst_n)
                   !mem_dma_bus |-> mem_dma_oe);

  // Ack must be a one-cycle pulse and only when "ready"
  assert property (@(posedge clk) disable iff (!rst_n) $rose(dma_ack) |-> ##1 !dma_ack);
  assert property (@(posedge clk) disable iff (!rst_n) dma_ack |-> dma_busynready);

  // End must be a one-cycle pulse and occurs with bus asserted
  assert property (@(posedge clk) disable iff (!rst_n) $rose(dma_end) |-> ##1 !dma_end);
  assert property (@(posedge clk) disable iff (!rst_n) dma_end |-> mem_dma_bus);

  // Read transaction: after bus drive starts with read, next cycle signals done and data captured
  assert property (@(posedge clk) disable iff (!rst_n)
                   $rose(mem_dma_bus) && mem_dma_rnw |->
                   ##1 (dma_end && !dma_ack && !dma_busynready && (dma_rd==mem_dma_rd)));

  // Write transaction: after bus drive starts with write, next cycle signals done
  assert property (@(posedge clk) disable iff (!rst_n)
                   $rose(mem_dma_bus) && !mem_dma_rnw |->
                   ##1 (dma_end && !dma_ack && !dma_busynready));

  // Write enable behavior (negedge domain)
  assert property (@(negedge clk) disable iff (!rst_n)
                   (mem_dma_rnw || !mem_dma_bus) |-> mem_dma_we==1'b1);

  assert property (@(negedge clk) disable iff (!rst_n)
                   (mem_dma_bus && !mem_dma_rnw) |-> (mem_dma_we == ~$past(mem_dma_we)));

  // Dropping request returns to idle (bus released, request deasserted next cycle)
  assert property (@(posedge clk) disable iff (!rst_n)
                   $fell(dma_req) |-> ##1 (!mem_dma_bus && busrq_n));

  // Safety: OE low implies read and bus driven; write implies OE high
  assert property (@(posedge clk) disable iff (!rst_n) !mem_dma_oe |-> (mem_dma_rnw && mem_dma_bus));
  assert property (@(posedge clk) disable iff (!rst_n) !mem_dma_rnw |-> mem_dma_oe);

  // --------------------------
  // Functional coverage
  // --------------------------

  // Cover a full read beat from request through grant to data return
  cover property (@(posedge clk) disable iff (!rst_n)
    $fell(busrq_n) ##[1:$] (!busak_n) ##1
    (mem_dma_bus && mem_dma_rnw && !mem_dma_oe) ##1
    (dma_end && !dma_ack && !dma_busynready));

  // Cover a full write beat from request through grant to end
  cover property (@(posedge clk) disable iff (!rst_n)
    $fell(busrq_n) ##[1:$] (!busak_n) ##1
    (mem_dma_bus && !mem_dma_rnw && mem_dma_oe) ##1
    (dma_end && !dma_ack && !dma_busynready));

  // Cover back-to-back read then write while request stays asserted
  cover property (@(posedge clk) disable iff (!rst_n)
    $fell(busrq_n) ##[1:$] (!busak_n) ##1
    (mem_dma_bus && mem_dma_rnw) ##1
    (dma_end && dma_req) ##1
    (mem_dma_bus && !mem_dma_rnw));

  // Cover back-to-back write then read while request stays asserted
  cover property (@(posedge clk) disable iff (!rst_n)
    $fell(busrq_n) ##[1:$] (!busak_n) ##1
    (mem_dma_bus && !mem_dma_rnw) ##1
    (dma_end && dma_req) ##1
    (mem_dma_bus && mem_dma_rnw));

  // Cover cancellation before grant (no bus drive)
  cover property (@(posedge clk) disable iff (!rst_n)
    $rose(dma_req) ##[1:5] $fell(dma_req) ##1 (busrq_n && !mem_dma_bus));

  // Cover a write WE toggle
  cover property (@(negedge clk) disable iff (!rst_n)
    mem_dma_bus && !mem_dma_rnw ##1 (mem_dma_we != $past(mem_dma_we)));

endmodule

bind dma_access dma_access_sva u_dma_access_sva (.*);