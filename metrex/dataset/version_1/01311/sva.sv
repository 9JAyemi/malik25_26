// SVA for johnson_code
// Checks pipeline delays, functional update, and covers key Johnson behavior.

module johnson_code_sva (
  input  logic        clk,
  input  logic [4:0]  johnson_out,
  input  logic [4:0]  pipeline1,
  input  logic [4:0]  pipeline2,
  input  logic [4:0]  pipeline3,
  input  logic [4:0]  pipeline4
);

  default clocking cb @(posedge clk); endclocking

  // Simple history enable to safely use $past with depth up to 5
  logic [5:0] hist_en;
  always_ff @(posedge clk) hist_en <= {hist_en[4:0], 1'b1};

  // Pipeline correctness (each stage is johnson_out delayed by its depth)
  assert property (hist_en[1] |-> pipeline1 == $past(johnson_out,1));
  assert property (hist_en[2] |-> pipeline2 == $past(johnson_out,2));
  assert property (hist_en[3] |-> pipeline3 == $past(johnson_out,3));
  assert property (hist_en[4] |-> pipeline4 == $past(johnson_out,4));

  // Functional update across the 5-cycle retiming:
  // johnson_out(t) = {johnson_out(t-5)[3:0], ~johnson_out(t-5)[4]}
  assert property (hist_en[5] |-> johnson_out == {$past(johnson_out,5)[3:0], ~$past(johnson_out,5)[4]});

  // Direct feedback path uses pipeline4 from the previous cycle
  assert property (hist_en[1] |-> johnson_out == {$past(pipeline4,1)[3:0], ~$past(pipeline4,1)[4]});

  // Coverage: observe canonical Johnson transitions (sampled on the 5-cycle cadence)
  cover property (hist_en[5] && johnson_out == 5'b00000 ##5 johnson_out == 5'b10000);
  cover property (hist_en[5] && johnson_out == 5'b11111 ##5 johnson_out == 5'b01111);

  // Coverage: show a full Johnson step every 5 cycles, repeated 10 times (50 cycles total)
  // This also implicitly covers the 50-cycle periodicity once on-cycle.
  cover property (hist_en[5]
                  ##5 (johnson_out == {$past(johnson_out,5)[3:0], ~$past(johnson_out,5)[4]})
                  ##5 (johnson_out == {$past(johnson_out,5)[3:0], ~$past(johnson_out,5)[4]})
                  ##5 (johnson_out == {$past(johnson_out,5)[3:0], ~$past(johnson_out,5)[4]})
                  ##5 (johnson_out == {$past(johnson_out,5)[3:0], ~$past(johnson_out,5)[4]})
                  ##5 (johnson_out == {$past(johnson_out,5)[3:0], ~$past(johnson_out,5)[4]})
                  ##5 (johnson_out == {$past(johnson_out,5)[3:0], ~$past(johnson_out,5)[4]})
                  ##5 (johnson_out == {$past(johnson_out,5)[3:0], ~$past(johnson_out,5)[4]})
                  ##5 (johnson_out == {$past(johnson_out,5)[3:0], ~$past(johnson_out,5)[4]})
                  ##5 (johnson_out == {$past(johnson_out,5)[3:0], ~$past(johnson_out,5)[4]})
                  ##5 (johnson_out == {$past(johnson_out,5)[3:0], ~$past(johnson_out,5)[4]}));

  // Optional: cover eventual 50-cycle periodicity (once the design is on the Johnson cycle)
  cover property (hist_en[55] && (johnson_out == $past(johnson_out,50)));

endmodule

// Bind to the DUT (accessing internal pipelines)
bind johnson_code johnson_code_sva sva (
  .clk(clk),
  .johnson_out(johnson_out),
  .pipeline1(pipeline1),
  .pipeline2(pipeline2),
  .pipeline3(pipeline3),
  .pipeline4(pipeline4)
);