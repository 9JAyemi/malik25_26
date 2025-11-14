// SVA for shift_register
// Bind-friendly, concise, and checks next-state behavior and observability via ports only.

module shift_register_sva (
  input clk,
  input load,
  input [3:0] data_in,
  input shift_in,
  input [3:0] data_out,
  input shift_out
);
  default clocking cb @(posedge clk); endclocking

  // Guard for using $past
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Combinational aliasing
  assert property (shift_out == data_out[3]);

  // Next-state on load
  assert property (past_valid && $past(load) |-> data_out == $past(data_in));
  assert property (past_valid && $past(load) |-> shift_out == $past(data_in[3]));

  // Next-state on shift (no load)
  assert property (past_valid && !$past(load) |-> data_out == {$past(shift_in), $past(data_out[3:1])});
  assert property (past_valid && !$past(load) |-> shift_out == $past(shift_in));

  // 4-cycle shift pipeline consistency when continuously shifting
  assert property ((!load)[*4] |-> data_out == {
                      $past(shift_in,1), $past(shift_in,2),
                      $past(shift_in,3), $past(shift_in,4)
                   });

  // Coverage
  cover property (load);
  cover property (!load && shift_in == 1'b0);
  cover property (!load && shift_in == 1'b1);
  cover property (load ##1 (!load)[*3]);          // load then shift for a few cycles
  cover property ((!load)[*4]);                    // 4 consecutive shifts
endmodule

// Bind into the DUT
bind shift_register shift_register_sva sva (
  .clk(clk),
  .load(load),
  .data_in(data_in),
  .shift_in(shift_in),
  .data_out(data_out),
  .shift_out(shift_out)
);