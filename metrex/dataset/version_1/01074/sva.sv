// SVA checker for decoder
module decoder_sva (
  input logic                clk,
  input logic [63:0]         probe0, probe1, probe7, probe12,
  input logic [0:0]          probe2, probe3, probe4, probe5, probe6,
  input logic [0:0]          probe8, probe9, probe10, probe11,
  input logic [0:0]          probe13, probe14, probe15, probe16, probe17,
  input logic [63:0]         probe0_unused, probe1_unused, probe12_unused, // placeholders if needed
  input logic [7:0]          probe18, probe24,
  input logic [8:0]          probe19,
  input logic [0:0]          probe20, probe23,
  input logic [2:0]          probe21, probe22,
  input logic [63:0]         output0, output2,
  input logic                output1,
  input logic [7:0]          output3,
  input logic [8:0]          output4
);

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // No X/Z on outputs (after first cycle)
  assert property (past_valid |-> !$isunknown({output0, output1, output2, output3, output4}));

  // Core functional checks (registered, with truncation semantics)
  assert property (past_valid |-> output0 == $past(probe1)); // {probe0,probe1} -> low 64b = probe1
  assert property (past_valid |-> output2 == $past(probe12)); // {probe7,probe12} -> low 64b = probe12
  assert property (past_valid |-> output3 == $past(probe24)); // {probe18,probe24} -> low 8b  = probe24
  assert property (past_valid |-> output4 == {$past(probe19[2:0]), $past(probe21), $past(probe22)}); // low 9b

  // Reduction AND correctness (ensure inputs known, then check)
  assert property (past_valid |-> !$isunknown({probe2,probe3,probe4,probe5,probe6}));
  assert property (past_valid |-> output1 == $past(&{probe2,probe3,probe4,probe5,probe6}));

  // Minimal functional coverage
  cover property (past_valid && (output1 == 1'b1));
  cover property (past_valid && (output1 == 1'b0));

  // Exercise truncation cases (discarded upper bits became non-zero)
  cover property (past_valid && ($past(probe0)          != 64'd0));      // upper half of {probe0,probe1}
  cover property (past_valid && ($past(probe7)          != 64'd0));      // upper half of {probe7,probe12}
  cover property (past_valid && ($past(probe18)         != 8'd0));       // upper half of {probe18,probe24}
  cover property (past_valid && ($past(probe19[8:3])    != 6'd0));       // upper 6b truncated from {probe19,probe21,probe22}

endmodule

// Bind into DUT
bind decoder decoder_sva u_decoder_sva (.*);