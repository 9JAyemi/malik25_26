// SVA checker for converter
// Concise, high-quality functional checks + coverage
module converter_sva(input logic [3:0] in, input logic [3:0] out);

  // Golden mapping: out = floor((in+1)/2)
  function automatic logic [3:0] map(input logic [3:0] i);
    map = ({1'b0,i} + 5'd1) >> 1; // avoid 4-bit wrap on 15+1
  endfunction

  // Functional correctness (checked on any in/out activity; evaluated after DUT updates)
  // Uses ##0 to move sampling to Observed region for same-timestep combinational correctness
  assert property (@(in or out) 1'b1 |-> ##0 (out == map(in)))
    else $error("converter: out != map(in). in=%0d out=%0d exp=%0d", in, out, map(in));

  // Output range safety
  assert property (@(out) 1'b1 |-> ##0 (out <= 4'd8))
    else $error("converter: out out of range (>8). out=%0d", out);

  // X/Z checks on activity
  assert property (@(in) 1'b1 |-> ##0 !$isunknown(in))
    else $error("converter: X/Z on input detected. in=%b", in);
  assert property (@(out) 1'b1 |-> ##0 !$isunknown(out))
    else $error("converter: X/Z on output detected. out=%b", out);

  // Monotonicity: if input increases (decreases), output does not decrease (increase)
  assert property (@(in)
                   (!$isunknown(in) && !$isunknown($past(in)) && (in > $past(in)))
                   |-> ##0 (out >= $past(out)))
    else $error("converter: non-monotonic increase. prev in/out=%0d/%0d curr in/out=%0d/%0d",
                $past(in), $past(out), in, out);

  assert property (@(in)
                   (!$isunknown(in) && !$isunknown($past(in)) && (in < $past(in)))
                   |-> ##0 (out <= $past(out)))
    else $error("converter: non-monotonic decrease. prev in/out=%0d/%0d curr in/out=%0d/%0d",
                $past(in), $past(out), in, out);

  // Full input space coverage with correctness observed after update
  genvar i;
  for (i = 0; i < 16; i++) begin : C_IN_ALL
    localparam logic [3:0] EXP = ({1'b0,i} + 5'd1) >> 1;
    cover property (@(in) ##0 (in == i && out == EXP));
  end

endmodule

// Bind into the DUT
bind converter converter_sva u_converter_sva(.in(in), .out(out));