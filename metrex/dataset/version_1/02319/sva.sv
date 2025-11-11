// SVA for counter and its ROM

module counter_sva #(parameter int AWIDTH_P = 8)(
  input  logic              clk,
  input  logic              ce,
  input  logic [7:0]        q,
  input  logic [AWIDTH_P-1:0] addr,
  input  logic              ce0,
  input  logic [7:0]        data
);
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // Static/width checks
  initial begin
    assert (AWIDTH_P == 8) else $error("AWIDTH must be 8 to match ROM ports");
    assert ($bits(q)    == 8);
    assert ($bits(addr) == $bits(q));
  end

  // Constant ties
  assert property (addr == q);
  assert property (ce0  == ce);

  // Counter behavior
  assert property (past_valid &&  ce |-> q == $past(q) + 8'd1);
  assert property (past_valid && !ce |-> q == $past(q));
  assert property (past_valid && $past(ce) && $past(q)==8'hFF |-> q==8'h00);

  // Sanity (no X after first cycle)
  assert property (past_valid |-> !$isunknown({ce,q}));

  // ROM interface observations at top
  assert property (past_valid && !ce0 |-> data == $past(data));
  assert property (past_valid && data != $past(data) |-> $past(ce0));

  // Coverage
  cover property (past_valid && ce);                 // increment seen
  cover property (past_valid && !ce);                // hold seen
  cover property (past_valid && q==8'hFF && ce);     // wrap trigger
  cover property (past_valid && $past(ce));          // ROM read enable exercised
endmodule

bind counter counter_sva #(.AWIDTH_P(AWIDTH)) u_counter_sva (
  .clk  (clk),
  .ce   (ce),
  .q    (q),
  .addr (addr),
  .ce0  (ce0),
  .data (data)
);

// ROM-level SVA

module rom_sva (
  input  logic        clk,
  input  logic        ce0,
  input  logic [7:0]  addr0,
  input  logic [7:0]  q0
);
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // Enable gating and qualified updates
  assert property (past_valid && !ce0 |-> q0 == $past(q0));
  assert property (past_valid && q0 != $past(q0) |-> $past(ce0));

  // Coverage
  cover property (past_valid && ce0);
endmodule

bind Loop_loop_height_jbC_rom rom_sva u_rom_sva (
  .clk  (clk),
  .ce0  (ce0),
  .addr0(addr0),
  .q0   (q0)
);