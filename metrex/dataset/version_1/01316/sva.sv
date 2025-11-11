// SVA bind file for top_module and its internals
// Concise, high-signal-quality checks with key functional coverage

module top_module_sva (
  input clk,
  input reset,
  input [3:0] d,
  input select,
  input [3:0] count_out,
  input [3:0] mux_out,
  input [3:0] adder_out,
  input [3:0] final_out
);
  default clocking cb @(posedge clk); endclocking

  // Basic known-value checks at clock boundaries (helps catch X/Z propagation)
  assert property (cb !$isunknown({count_out, mux_out, adder_out, final_out}));

  // Counter next-state function (synchronous reset, modulo-16 increment)
  assert property (cb $past(1'b1) |-> count_out == ($past(reset) ? 4'h0 : $past(count_out) + 4'd1));

  // Mux function
  assert property (cb mux_out == (select ? d : count_out));

  // Adder function (4-bit wrap)
  assert property (cb adder_out == ((mux_out + count_out) & 4'hF));

  // Pipeline register: final_out is 1-cycle delayed adder_out
  assert property (cb $past(1'b1) |-> final_out == $past(adder_out));

  // End-to-end 1-cycle functional equivalence (ties all blocks together)
  assert property (cb $past(1'b1) |-> final_out == ((($past(select) ? $past(d) : $past(count_out)) + $past(count_out)) & 4'hF));

  // Key functional coverage
  // Reset deassertion seen
  cover property (cb reset ##1 !reset);

  // Counter wrap-around 15 -> 0 (no reset)
  cover property (cb $past(1'b1) && !$past(reset) && ($past(count_out)==4'hF) && (count_out==4'h0));

  // Mux both paths exercised
  cover property (cb select);
  cover property (cb !select);

  // Adder carry/overflow cases (5th bit carry)
  cover property (cb ({1'b0, mux_out} + {1'b0, count_out})[4]);

  // Select=0 path (doubling count) causes wrap
  cover property (cb !select && ({1'b0, count_out} + {1'b0, count_out})[4]);

  // Select=1 path causes wrap
  cover property (cb select && ({1'b0, d} + {1'b0, count_out})[4]);
endmodule

bind top_module top_module_sva u_top_module_sva (.*);