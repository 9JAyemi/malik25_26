// SVA for top_module and decoder_2to4_with_enable
// Focused, concise checks + coverage

// Bind into top_module
module top_module_sva (
  input clk, input rst_n,
  input a, input [4:0] in,
  input out_and, input out_or, input out_nor, input final_output,
  input a_prev, input edge_detected, input [1:0] decoder_out
);
  // Reset values
  assert property (@(posedge clk) !rst_n |-> (a_prev==0 && edge_detected==0 && final_output==0));

  // Edge-detect and a_prev correctness
  assert property (@(posedge clk) disable iff (!rst_n)
                   $past(rst_n) |-> (a_prev == $past(a)));
  assert property (@(posedge clk) disable iff (!rst_n)
                   $past(rst_n) |-> (edge_detected == (a ^ $past(a))));

  // Combinational outputs correct and consistent
  assert property (@(posedge clk) out_and == (&in));
  assert property (@(posedge clk) out_or  == (|in));
  assert property (@(posedge clk) out_nor == (~|in));
  assert property (@(posedge clk) out_nor == ~out_or);
  assert property (@(posedge clk) out_and |-> out_or);   // all-ones implies any-one

  // final_output behavior (flag X on decoder_out)
  assert property (@(posedge clk) disable iff (!rst_n)
                   !$isunknown(decoder_out)); // decoder_out must be driven/known
  assert property (@(posedge clk) disable iff (!rst_n)
                   $past(rst_n) && !$isunknown(decoder_out[1])
                   |-> (final_output == (edge_detected & decoder_out[1])));
  assert property (@(posedge clk) disable iff (!rst_n)
                   final_output |-> edge_detected);

  // No X/Z on primary outputs
  assert property (@(posedge clk) !$isunknown({out_and,out_or,out_nor,final_output}));

  // Coverage
  cover property (@(posedge clk) disable iff (!rst_n) $rose(a));
  cover property (@(posedge clk) disable iff (!rst_n) $fell(a));
  cover property (@(posedge clk) disable iff (!rst_n) (&in)  && out_and &&  out_or && !out_nor); // all 1s
  cover property (@(posedge clk) disable iff (!rst_n) (~|in) && !out_and && !out_or &&  out_nor); // all 0s
  cover property (@(posedge clk) disable iff (!rst_n) edge_detected && decoder_out==2 && final_output);
  cover property (@(posedge clk) disable iff (!rst_n) edge_detected && decoder_out==3 && final_output);
endmodule

bind top_module top_module_sva top_module_sva_i (
  .clk(clk), .rst_n(rst_n),
  .a(a), .in(in),
  .out_and(out_and), .out_or(out_or), .out_nor(out_nor), .final_output(final_output),
  .a_prev(a_prev), .edge_detected(edge_detected), .decoder_out(decoder_out)
);

// SVA for decoder_2to4_with_enable
module decoder_2to4_with_enable_sva (input in, input en, input [1:0] out);
  // Functional equivalence (case maps to concatenation)
  assert property (@(*) out == {in,en});

  // Full input space coverage
  cover property (@(*) {in,en}==2'b00 && out==2'b00);
  cover property (@(*) {in,en}==2'b01 && out==2'b01);
  cover property (@(*) {in,en}==2'b10 && out==2'b10);
  cover property (@(*) {in,en}==2'b11 && out==2'b11);

  // Outputs known
  assert property (@(*) !$isunknown(out));
endmodule

bind decoder_2to4_with_enable decoder_2to4_with_enable_sva decoder_2to4_with_enable_sva_i (
  .in(in), .en(en), .out(out)
);