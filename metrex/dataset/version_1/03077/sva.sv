// SVA for top_module and its sub-block behavior
// Focus: comparator correctness, counter sequencing, output selection, and concise functional coverage

module top_module_sva (
    input  logic        clk,
    input  logic        reset,
    input  logic [3:0]  data_in,
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic        load,
    input  logic [7:0]  out,
    input  logic        GT,
    input  logic        EQ,
    input  logic [3:0]  counter_out
);
  default clocking cb @(posedge clk); endclocking

  // Comparator correctness and sanity
  assert property (GT == (A > B));
  assert property (EQ == (A == B));
  assert property (!(GT && EQ));

  // Counter behavior (synchronous reset, load, increment, wrap)
  assert property (reset |=> counter_out == 4'h0);
  assert property (!reset && load |=> counter_out == data_in);
  assert property (!reset && !load && $past(counter_out) != 4'hF |=> counter_out == $past(counter_out) + 1);
  assert property (!reset && !load && $past(counter_out) == 4'hF |=> counter_out == 4'h0);

  // No X on key outputs when not in reset
  assert property (!reset |-> !$isunknown({counter_out, GT, EQ, out})); 

  // Output selection correctness and priority
  assert property (out[7:4] == 4'h0);
  assert property (GT |-> (out[3:0] == A));
  assert property (!GT && EQ |-> (out[3:0] == B));
  assert property (!GT && !EQ |-> (out[3:0] == counter_out));

  // Functional coverage
  cover property (reset ##1 !reset);                         // reset observed and released
  cover property (load && !reset);                           // load used
  cover property (!reset && !load && $past(counter_out)==4'hF && counter_out==4'h0); // wrap
  cover property (GT);                                       // A > B path
  cover property (!GT && EQ);                                // A == B path
  cover property (!GT && !EQ);                               // A < B path
  cover property (!GT && !EQ ##1 GT);                        // LT to GT transition exercised
  cover property (GT ##1 (!GT && EQ));                       // GT to EQ transition exercised
endmodule

bind top_module top_module_sva sva_i (
  .clk(clk),
  .reset(reset),
  .data_in(data_in),
  .A(A),
  .B(B),
  .load(load),
  .out(out),
  .GT(GT),
  .EQ(EQ),
  .counter_out(counter_out)
);