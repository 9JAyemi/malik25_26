// SVA for shift_register
module shift_register_sva(
  input logic        clk,
  input logic        shift,
  input logic        in,
  input logic        out,
  input logic [3:0]  reg_out
);
  default clocking @(posedge clk); endclocking

  logic past_valid; initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Single-cycle functional correctness
  assert property (disable iff (!past_valid)
    shift |-> reg_out == { $past(reg_out)[2:0], $past(in) });

  assert property (disable iff (!past_valid)
    !shift |-> reg_out == { $past(in), $past(reg_out)[3:1] });

  // Output wiring and cycle-accurate effect on out
  assert property (@(posedge clk) out === reg_out[0]);

  assert property (disable iff (!past_valid)
    shift |-> out == $past(in));

  assert property (disable iff (!past_valid)
    !shift |-> out == $past(reg_out[1]));

  // Minimal, meaningful coverage
  cover property (disable iff (!past_valid) shift [*4]);            // 4 consecutive left shifts
  cover property (disable iff (!past_valid) !shift [*4]);           // 4 consecutive right shifts
  cover property (disable iff (!past_valid) shift ##1 !shift ##1 shift ##1 !shift); // alternation
  cover property (disable iff (!past_valid) out != $past(out));     // out toggles
  cover property (disable iff (!past_valid) shift && in ##1 out);   // left shift, drive 1 through
  cover property (disable iff (!past_valid) shift && !in ##1 !out); // left shift, drive 0 through
endmodule

// Bind into DUT (access internal reg_out)
bind shift_register shift_register_sva u_shift_register_sva(
  .clk(clk),
  .shift(shift),
  .in(in),
  .out(out),
  .reg_out(reg_out)
);