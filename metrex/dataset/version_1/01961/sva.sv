// SVA for snoop_module
// Bind-friendly; includes a small shadow model for memory to check q timing.

module snoop_module_sva
(
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  snoopa,
  input  logic [7:0]  snoopd,
  input  logic        snoopp,
  input  logic        snoopq,
  input  logic        snoopm,
  ref    logic [7:0]  prgram [0:255],
  input  int          i
);

  // Shadow model of memory contents (post-NBA state each cycle)
  logic [7:0] model [0:255];
  bit         valid [0:255];

  always_ff @(posedge clk) begin
    if (reset) begin
      foreach (valid[idx]) valid[idx] <= 1'b0;
    end else if (snoopp) begin
      model[snoopa] <= snoopd;
      valid[snoopa] <= 1'b1;
    end
  end

  // q reflects previous cycle's memory at current address (when known)
  property p_q_prev_mem;
    int unsigned a;
    @(posedge clk) disable iff (reset)
      (1, a = snoopa, $past(valid[a])) |-> (snoopq == $past(model[a]));
  endproperty
  assert property (p_q_prev_mem);

  // Write updates memory by next clock edge
  assert property (@(posedge clk) disable iff (reset)
                   snoopp |=> prgram[$past(snoopa)] == $past(snoopd));

  // q resets to 0 when reset asserted
  assert property (@(posedge clk) reset |-> snoopq == 1'b0);

  // i reset behavior and next-state function (mod-256 up-counter)
  assert property (@(posedge clk) reset |-> i == 0);
  assert property (@(posedge clk) disable iff (reset)
                   ($past(i) == 255) |-> (i == 0));
  assert property (@(posedge clk) disable iff (reset)
                   ($past(i) != 255) |-> (i == $past(i)+1));

  // m mirrors (i == 255)
  assert property (@(posedge clk) snoopm == (i == 255));

  // Optional: knownness when data is expected to be valid
  assert property (@(posedge clk) disable iff (reset)
                   $past(valid[snoopa]) |-> !$isunknown(snoopq));

  // Coverage
  cover property (@(posedge clk) disable iff (reset)
                  (i == 255) ##1 (i == 0));
  // Write -> next-cycle address match -> data returns two cycles after write
  property p_wr_rd_latency;
    int unsigned a; logic [7:0] d;
    @(posedge clk) disable iff (reset)
      (snoopp, a = snoopa, d = snoopd)
      ##1 (snoopa == a && !(snoopp && snoopa == a))
      ##1 (snoopq == d);
  endproperty
  cover property (p_wr_rd_latency);

endmodule

// Bind into the DUT
bind snoop_module snoop_module_sva sva (
  .clk    (clk),
  .reset  (reset),
  .snoopa (snoopa),
  .snoopd (snoopd),
  .snoopp (snoopp),
  .snoopq (snoopq),
  .snoopm (snoopm),
  .prgram (prgram),
  .i      (i)
);