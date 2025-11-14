// SVA for concat_module: bindable, concise, and high-quality checks

module concat_module_sva (
  input clk,
  input [89:0] in,
  input [44:0] line0,
  input [44:0] line1,
  input [89:0] out
);
  default clocking cb @(posedge clk); endclocking

  // Warm-up to avoid $past at time 0
  logic warm1, warm2;
  always @(posedge clk) begin
    warm1 <= 1'b1;
    warm2 <= warm1;
  end

  // 1-cycle slice capture into line regs
  a_line0_cap: assert property (warm1 |-> line0 === $past(in[44:0]));
  a_line1_cap: assert property (warm1 |-> line1 === $past(in[89:45]));

  // Out built from previous line regs (ensures proper NBA/ordering)
  a_out_from_lines: assert property (warm1 |-> out === {$past(line0), $past(line1)});

  // End-to-end behavior: 2-cycle latency and swapped halves from input
  a_out_from_in: assert property (warm2 |-> out === {$past(in[44:0],2), $past(in[89:45],2)});

  // Coverage: demonstrate swap effect and pipeline movement
  c_swap_seen: cover property (
    warm2 && (in[89:45] != in[44:0]) ##2
    (out[89:45] == $past(in[44:0],2) && out[44:0] == $past(in[89:45],2))
  );
  c_pipeline_moves: cover property (warm2 && (in !== $past(in)) ##2 (out !== $past(out)));

endmodule

// Bind into the DUT
bind concat_module concat_module_sva sva (.clk(clk), .in(in), .line0(line0), .line1(line1), .out(out));