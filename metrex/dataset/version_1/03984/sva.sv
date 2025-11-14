// SVA for top_module: checks mux, counter, and out logic concisely with key coverage
module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [255:0] in,
  input  logic [7:0]  sel,
  input  logic [7:0]  mux_sel,
  input  logic [7:0]  mux_out,
  input  logic [3:0]  counter,
  input  logic [3:0]  q,
  input  logic [3:0]  out
);

  default clocking cb @(posedge clk); endclocking

  // Past-valid guard for $past()
  logic past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Basic sanity: no X/Z on key IOs
  assert property (cb (past_valid |-> !$isunknown(reset) && !$isunknown(sel) && !$isunknown(in) && !$isunknown(q) && !$isunknown(out)));

  // Synchronous reset drives counter/q to 0
  assert property (cb (reset |-> (q == 4'd0 && counter == 4'd0)));

  // q mirrors counter
  assert property (cb (q == counter));

  // Counter increments by 1 when not in/reset and prev cycle not reset
  assert property (cb (past_valid && !reset && !$past(reset) |-> q == $past(q) + 4'd1));

  // Wrap from F -> 0
  assert property (cb (past_valid && !reset && !$past(reset) && $past(q) == 4'hF |-> q == 4'h0));

  // First cycle after reset deassert goes to 1
  assert property (cb (past_valid && $past(reset) && !reset |-> q == 4'd1));

  // Mux select is pass-through
  assert property (cb (mux_sel == sel));

  // 256:1 mux functional check and width behavior
  assert property (cb (mux_out[0] == in[sel] && mux_out[7:1] == 7'b0));

  // Final out behavior (width/truncation semantics): only bit0 can propagate
  assert property (cb (out[3:1] == 3'b000 && out[0] == (in[sel] & q[0])));

  // Coverage
  cover property (cb (past_valid && $past(!reset) && !reset && $past(q)==4'hF && q==4'h0)); // wrap
  cover property (cb (!reset && out[0] == 1'b1));                                           // AND result high
  cover property (cb (sel == 8'h00));
  cover property (cb (sel == 8'hFF));
  cover property (cb ($fell(reset)));                                                       // reset release

endmodule

// Bind into DUT
bind top_module top_module_sva u_top_module_sva (
  .clk(clk),
  .reset(reset),
  .in(in),
  .sel(sel),
  .mux_sel(mux_sel),
  .mux_out(mux_out),
  .counter(counter),
  .q(q),
  .out(out)
);