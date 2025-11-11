// SVA for xor_adder
module xor_adder_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  in,
  input logic [3:0]  out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Functional correctness (lower nibble only matters)
  property p_func;
    out == (((in[3:0] ^ 4'hA) + 4'h1)[3:0]);
  endproperty
  assert property (p_func);

  // Synchronous reset holds zero
  property p_reset_sync;
    reset |-> (out == 4'h0);
  endproperty
  assert property (p_reset_sync);

  // Asynchronous reset drives zero immediately
  property p_reset_async;
    @(posedge reset) out == 4'h0;
  endproperty
  assert property (p_reset_async);

  // Output has no X/Z after reset deasserted
  property p_no_x_out;
    !$isunknown(out);
  endproperty
  assert property (p_no_x_out);

  // High nibble of input does not affect result
  property p_high_indep;
    (in[3:0] == $past(in[3:0])) |-> (out == $past(out));
  endproperty
  assert property (p_high_indep);

  // Coverage
  cover property (@(posedge reset) 1); // reset seen
  cover property ((in[3:0] ^ 4'hA) == 4'hF |-> (out == 4'h0)); // wrap to 0
  cover property ((in[3:0] == $past(in[3:0])) && (in[7:4] != $past(in[7:4])) |-> (out == $past(out))); // high-nibble change only

endmodule

// Bind into DUT
bind xor_adder xor_adder_sva sva(.clk(clk), .reset(reset), .in(in), .out(out));