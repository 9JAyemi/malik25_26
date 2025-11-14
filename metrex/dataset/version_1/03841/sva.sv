// SVA for shift_reg
module shift_reg_sva (
  input logic        clk,
  input logic        load,
  input logic [3:0]  data_in,
  input logic [3:0]  q
);

  default clocking cb @(posedge clk); endclocking

  // past_valid to safely use $past
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Sanity: no X/Z on control and inputs at sampling times
  assert property (!$isunknown({load, data_in}))
    else $error("shift_reg: X/Z on load or data_in at clk edge");

  // Functional correctness
  // Parallel load: on load, q should equal data_in on next cycle
  assert property ( (load && !$isunknown(data_in)) |=> q == $past(data_in) )
    else $error("shift_reg: parallel load mismatch (q != data_in)");

  // Serial shift: when not loading, shift left and bring in data_in[0]
  assert property ( (!load && !$isunknown({q[2:0], data_in[0]}))
                    |=> q == { $past(q[2:0]), $past(data_in[0]) } )
    else $error("shift_reg: shift behavior mismatch");

  // Coverage
  cover property (load |=> q == $past(data_in));                     // parallel load exercised
  cover property (!load |=> q == { $past(q[2:0]), $past(data_in[0]) }); // shift exercised

  // Mode transitions
  cover property (load ##1 !load);
  cover property (!load ##1 load);

  // Exercise both serial input values
  cover property (!load && (data_in[0] == 1'b0));
  cover property (!load && (data_in[0] == 1'b1));

  // Parallel load with corner patterns
  cover property (load && data_in == 4'h0);
  cover property (load && data_in == 4'hF);

  // Longer shift streak to exercise full pipeline length
  cover property (!load[*4]);

  // Back-to-back loads
  cover property (load[*2]);

endmodule

bind shift_reg shift_reg_sva sva_inst (.*);