// SVA for top_module and sub-functions
module top_module_sva (
  input  logic        clk,
  input  logic        reset,        // active-low
  input  logic [7:0]  in,
  input  logic [2:0]  pos,
  input  logic        d,
  input  logic [3:0]  q,
  input  logic        out
);
  default clocking cb @(posedge clk); endclocking

  // Environment sanity (avoid X/Z driven into combinational encoders)
  assume property (!$isunknown(in));
  assume property (!$isunknown(d));

  // Priority encoder correctness
  assert property ((in == 8'b0000_0001) |-> (pos == 3'd0));
  assert property ((in == 8'b0000_0010) |-> (pos == 3'd1));
  assert property ((in == 8'b0000_0100) |-> (pos == 3'd2));
  assert property ((in == 8'b0000_1000) |-> (pos == 3'd3));
  assert property ((in == 8'b0001_0000) |-> (pos == 3'd4));
  assert property ((in == 8'b0010_0000) |-> (pos == 3'd5));
  assert property ((in == 8'b0100_0000) |-> (pos == 3'd6));
  assert property ((in == 8'b1000_0000) |-> (pos == 3'd7));
  assert property ((!$onehot(in))       |-> (pos == 3'b111));  // default case only on non-onehot

  // Shift-register: async reset low forces/holds zero; functional shift on clk
  assert property (@(negedge reset) (q == 4'b0000));                 // immediate on negedge
  assert property (!reset |-> (q == 4'b0000));                       // held while low
  assert property (disable iff (!reset) q == { $past(q[2:0]), $past(d) }); // shift
  assert property (disable iff (!reset) !$isunknown(q));             // no X after release

  // Functional module relation
  assert property (out == (pos == q[3:1]));

  // Key coverage
  cover property (in == 8'b0000_0001 && pos == 3'd0);
  cover property (in == 8'b0000_0010 && pos == 3'd1);
  cover property (in == 8'b0000_0100 && pos == 3'd2);
  cover property (in == 8'b0000_1000 && pos == 3'd3);
  cover property (in == 8'b0001_0000 && pos == 3'd4);
  cover property (in == 8'b0010_0000 && pos == 3'd5);
  cover property (in == 8'b0100_0000 && pos == 3'd6);
  cover property (in == 8'b1000_0000 && pos == 3'd7);
  cover property (in == 8'b0000_0000 && pos == 3'b111);             // default mapping seen

  cover property (disable iff (!reset)
                  (q==4'b0001) ##1 (q==4'b0010) ##1 (q==4'b0100) ##1 (q==4'b1000)); // shift progression
  cover property (out == 1'b1);
  cover property (out == 1'b0);
endmodule

bind top_module top_module_sva sva_i (
  .clk   (clk),
  .reset (reset),
  .in    (in),
  .pos   (pos),
  .d     (d),
  .q     (q),
  .out   (out)
);