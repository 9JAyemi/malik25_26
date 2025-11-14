// SVA for shift_reg_serial
module shift_reg_serial_sva (
  input  logic                   clk,
  input  logic                   shift,
  input  logic                   data_in,
  input  logic                   q,
  input  logic [3:0]             pipeline [2:0]
);
  default clocking cb @(posedge clk); endclocking

  // Validity tracking for $past
  bit v1, v2, v3;
  always_ff @(posedge clk) begin
    v1 <= 1'b1;
    v2 <= v1;
    v3 <= v2;
  end

  // Sanity/X checks
  assert property (v1 |-> !$isunknown({shift, data_in}));
  assert property (v1 |-> !$isunknown({q, pipeline[0], pipeline[1], pipeline[2]}));

  // Upper bits of pipeline must remain zero (due to 1-bit sources)
  assert property (v2 |-> (pipeline[0][3:1]==3'b0 &&
                           pipeline[1][3:1]==3'b0 &&
                           pipeline[2][3:1]==3'b0));

  // Next-state relation for q (independent of shift)
  assert property (v1 |-> q == $past(pipeline[2][0]));

  // Next-state relations when not shifting (load new data_in)
  assert property (v1 && !shift |-> (pipeline[0] == {3'b0, $past(data_in)} &&
                                     pipeline[1] == $past(pipeline[0])     &&
                                     pipeline[2] == $past(pipeline[1])));

  // Next-state relations when shifting (recirculate via q)
  assert property (v1 &&  shift |-> (pipeline[0] == $past(pipeline[1])     &&
                                     pipeline[1] == $past(pipeline[2])     &&
                                     pipeline[2] == {3'b0, $past(q)}));

  // End-to-end latency: with 3 consecutive non-shift cycles, q reflects data_in from 3 cycles ago
  assert property (v3 and (!shift)[*3] |-> q == $past(data_in,3));

  // Under consecutive shift cycles, q is 2-cycle periodic
  assert property (v2 && shift && $past(shift) |-> q == $past(q,2));

  // Coverage
  cover property (v1 && !shift);
  cover property (v1 &&  shift);
  cover property (v3 and (!shift)[*3] ##1 (q == $past(data_in,3)));
  cover property (shift[*2]);
  cover property ($rose(shift));
  cover property ($fell(shift));
endmodule

bind shift_reg_serial shift_reg_serial_sva sva_i (
  .clk(clk),
  .shift(shift),
  .data_in(data_in),
  .q(q),
  .pipeline(pipeline)
);