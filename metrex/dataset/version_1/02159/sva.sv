// SVA for smr_reg
module smr_reg_sva #(
  parameter int width = 16,
  parameter int add_width = 13
)(
  input  logic                 clk,
  input  logic                 rst,
  input  logic                 we,
  input  logic                 incr,
  input  logic [width-1:0]     wr,
  input  logic [add_width-1:0] rd,
  input  logic [width-1:0]     mem
);

  localparam int W  = width;
  localparam int AW = add_width;

  default clocking cb @(posedge clk); endclocking

  // Parameter sanity
  initial assert (AW <= W) else $error("smr_reg: add_width (%0d) must be <= width (%0d)", AW, W);

  // Control inputs not X/Z
  assert property (!$isunknown({rst,we,incr})));

  // Reset behavior: clear next cycle and hold at zero while asserted
  assert property (rst |=> mem == {W{1'b0}});
  assert property (rst && $past(rst) |-> mem == {W{1'b0}});

  // Write path (priority over incr)
  assert property (!rst && we |=> mem == $past(wr));
  assert property (!rst && we && incr |=> mem == $past(wr));

  // Increment path (when no write)
  assert property (!rst && !we && incr |=> mem == $past(mem) + 1);

  // Hold path (no write, no incr)
  assert property (!rst && !we && !incr |=> mem == $past(mem));

  // rd mapping to low bits of mem
  assert property (rd == mem[AW-1:0]);

  // No X on rd when driving bits of mem are known
  assert property (!$isunknown(mem[AW-1:0]) |-> !$isunknown(rd));

  // Optional: mem should never go X after reset release
  assert property ($rose(!rst) |-> !$isunknown(mem));

  // Coverage
  cover property (rst ##1 mem == {W{1'b0}});
  cover property (!rst && we ##1 mem == $past(wr));
  cover property (!rst && !we && incr ##1 mem == $past(mem) + 1);
  cover property (!rst && we && incr ##1 mem == $past(wr)); // priority observed
  cover property (!rst && !we && !incr ##1 mem == $past(mem));
  cover property (!rst && !we && incr && $past(mem) == {W{1'b1}} ##1 mem == {W{1'b0}}); // wrap

endmodule

// Bind example (place in a separate bind file or in your testbench):
// bind smr_reg smr_reg_sva #(.width(width), .add_width(add_width))
//   svr (.*,.mem(mem));