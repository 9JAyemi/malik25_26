// SVA for top_module
module top_module_sva (
  input logic         clk,
  input logic         reset,
  input logic [7:0]   in,
  input logic [7:0]   anyedge,
  input logic [31:0]  transition_out,
  input logic [7:0]   final_reg,
  input logic [7:0]   final_out
);

  default clocking cb @(posedge clk); endclocking

  // Make $past well-defined
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Reset behavior (synchronous clear)
  // When reset is 1 on a clock edge, both transition_out and final_reg must be 0 that cycle,
  // and final_out must be 0 as well.
  assert property (reset |-> (transition_out == 32'b0 && final_reg == 8'b0 && final_out == 8'b0));

  // anyedge must equal combinational function of the registered input (reg_in == $past(in))
  assert property (disable iff (reset)
    anyedge == ($past(in) & ~{ $past(in)[6:0], 1'b0 })
  );

  // transition_capture shift behavior: out <= {out[30:0], in} with in = anyedge[0] (sampled previous cycle)
  assert property (disable iff (reset)
    transition_out == { $past(transition_out[30:0]), $past(anyedge[0]) }
  );

  // final_reg mapping from transition_out (uses previous cycle's transition_out)
  assert property (disable iff (reset)
    final_reg == { {4{$past(transition_out[31])}}, $past(transition_out[30:27]) }
  );

  // final_out combinational mask by ~anyedge
  assert property (final_out == (final_reg & ~anyedge));

  // No X/Z on key observable signals after reset deasserted
  assert property (disable iff (reset)
    !$isunknown({anyedge, transition_out, final_reg, final_out})
  );

  // Coverage
  // 1) Exit reset
  cover property (reset ##1 !reset);

  // 2) Capture of a '1' into transition_out[0] from anyedge[0]
  cover property (disable iff (reset) $past(anyedge[0]) && transition_out[0]);

  // 3) Replication path observed on final_out[7:4] (no masking on top nibble)
  cover property (disable iff (reset)
    (anyedge[7:4] == 4'b0000) && transition_out[31] && (final_out[7:4] == 4'hF)
  );

  // 4) Bottom nibble passes through (no masking) from transition_out[30:27]
  cover property (disable iff (reset)
    (anyedge[3:0] == 4'b0000) && (final_out[3:0] == transition_out[30:27])
  );

  // 5) Masking active on at least one bit
  cover property (disable iff (reset)
    (|anyedge) && ((final_out & anyedge) == '0)
  );

endmodule

// Bind into DUT (accessing internal signals)
bind top_module top_module_sva sva_top (
  .clk(clk),
  .reset(reset),
  .in(in),
  .anyedge(anyedge),
  .transition_out(transition_out),
  .final_reg(final_reg),
  .final_out(final_out)
);