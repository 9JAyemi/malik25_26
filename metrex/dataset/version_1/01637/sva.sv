// SVA for the provided design. Bind to top_module.
// Concise checks for reset, next-state, combinational correctness, X-prop, and key coverage.

module top_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [254:0] in,
  input  logic [7:0]  out,
  input  logic [3:0]  johnson_out,
  input  logic [7:0]  population_out
);
  default clocking cb @(posedge clk); endclocking

  // johnson_counter: async/sync reset behavior
  assert property (@(negedge rst_n) johnson_out == 4'b0);
  assert property ( !rst_n |-> johnson_out == 4'b0 );

  // johnson_counter: next-state function
  assert property ( $past(rst_n) && rst_n |-> 
                    johnson_out == { $past(johnson_out[2:0]), $past(johnson_out[3]) ^ $past(johnson_out[0]) } );

  // population_count: correctness vs $countones
  assert property ( population_out == $countones(in) );

  // and_module: bitwise AND (including zero-extended high nibble)
  assert property ( out == {4'b0, (johnson_out & population_out[3:0])} );

  // top-level: output forced low in reset
  assert property ( !rst_n |-> out == 8'h00 );

  // X-propagation clean when inputs known
  assert property ( !$isunknown({rst_n,in}) |-> !$isunknown({johnson_out, population_out, out}) );

  // Coverage
  cover property ( $rose(rst_n) );
  cover property ( population_out == 8'd0 );
  cover property ( population_out == 8'd255 );
  cover property ( rst_n && $changed(johnson_out) );
endmodule

bind top_module top_sva i_top_sva (
  .clk(clk),
  .rst_n(rst_n),
  .in(in),
  .out(out),
  .johnson_out(johnson_out),
  .population_out(population_out)
);