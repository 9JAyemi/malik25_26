// SVA for the provided design. Focused, high-signal-coverage, concise.
// Bind these into the DUT; no DUT edits required.

//////////////////////////////////////////////////////////////
// Top-level connectivity/behavior checks
//////////////////////////////////////////////////////////////
module top_module_sva (
  input  logic         clk,
  input  logic         reset,         // active-low for JC
  input  logic [127:0] final_output,
  input  logic [127:0] jc_output,
  input  logic [127:0] dff_output,
  input  logic [15:0]  jc_input
);

  // final_output is a left-shifted concatenation; due to truncation:
  // final_output[127:112] mirrors jc_output[15:0], lower 112 bits are 0.
  assert property (@(posedge clk)
    final_output === {jc_output[15:0], 112'h0}
  ) else $error("final_output shape/content mismatch");

  // Wiring into jc_input must match the RTL intent (with truncation on [0])
  assert property (@(posedge clk) jc_input[0]  === dff_output[0])
    else $error("jc_input[0] must equal dff_output[0]");
  genvar i;
  generate
    for (i = 0; i < 15; i++) begin : G_JC_IN
      assert property (@(posedge clk) jc_input[i+1] === jc_output[i])
        else $error("jc_input[%0d] must equal jc_output[%0d]", i+1, i);
    end
  endgenerate

  // When reset is asserted low, JC should output 16'h0001 in its low 16 bits,
  // therefore final_output[127:112] must be 16'h0001 as well.
  assert property (@(posedge clk)
    !reset |-> (final_output === {16'h0001, 112'h0})
  ) else $error("Reset-to-known value not observed on final_output");

  // Coverage: see a non-zero final_output MSW and a reset pulse
  cover property (@(posedge clk) final_output[127:112] != 16'h0);
  cover property (@(posedge clk) !reset ##1 reset);

endmodule

bind top_module top_module_sva u_top_module_sva (
  .clk(clk),
  .reset(reset),
  .final_output(final_output),
  .jc_output(jc_output),
  .dff_output(dff_output),
  .jc_input(jc_input)
);

//////////////////////////////////////////////////////////////
// DFF_module functional check
//////////////////////////////////////////////////////////////
module DFF_module_sva (
  input  logic         clk,
  input  logic         d,
  input  logic [127:0] q
);
  // Intent in RTL implies width-mismatch zero-extend; check observed behavior:
  // q must be {1'b0, {127{d}}} at each rising edge.
  assert property (@(posedge clk)
    q === {1'b0, {127{d}}}
  ) else $error("DFF_module q mismatch (MSB must be 0; remaining all d)");

  // Coverage: see both d=0 and d=1
  cover property (@(posedge clk) d==1'b0);
  cover property (@(posedge clk) d==1'b1);
endmodule

bind DFF_module DFF_module_sva u_DFF_module_sva (
  .clk(clk),
  .d(d),
  .q(q)
);

//////////////////////////////////////////////////////////////
// Johnson/feedback counter checks
//////////////////////////////////////////////////////////////
module JC_counter_sva (
  input  logic         clk,
  input  logic         rst_n,   // active-low
  input  logic [127:0] Q
);

  // Reset behavior: on any clock with rst_n low, Q[15:0]==16'h0001 and upper bits zero
  assert property (@(posedge clk)
    !rst_n |-> (Q[15:0]==16'h0001 && Q[127:16]==0)
  ) else $error("JC reset value incorrect");

  // Upper bits of Q are always zero (zero-extension from 16-bit reg)
  assert property (@(posedge clk)
    Q[127:16]==0
  ) else $error("JC upper bits must remain zero");

  // Next-state function (disable during reset): Johnson/LFSR-like recurrence
  assert property (@(posedge clk) disable iff (!rst_n)
    Q[15:0] == { $past(Q[14:0]), ~($past(Q[14]) ^ $past(Q[15])) }
  ) else $error("JC next-state relation violated");

  // Coverage: see at least one state transition after reset released
  cover property (@(posedge clk) disable iff (!rst_n) $changed(Q[15:0]));
  cover property (@(posedge clk) $rose(rst_n));
endmodule

bind chatgpt_generate_JC_counter JC_counter_sva u_JC_counter_sva (
  .clk(clk),
  .rst_n(rst_n),
  .Q(Q)
);