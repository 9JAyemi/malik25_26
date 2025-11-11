// SVA for glitch_filter
// Bind-friendly, concise, checks shift behavior and exact temp_out/out function

module glitch_filter_sva #(parameter int n = 4)
(
  input  logic                clk,
  input  logic                in,
  input  logic                out,
  input  logic [n-1:0]        shift_reg,
  input  logic                temp_out
);

  // Parameter sanity
  initial if (n < 4) $fatal(1, "glitch_filter requires n>=4 (uses n-1..n-3)");

  // Past-valid guard (no reset in DUT)
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Out is just temp_out
  assert property (@(posedge clk) out == temp_out);

  // Shift register behavior (RHS uses pre-update values)
  assert property (@(posedge clk) disable iff(!past_valid)
    shift_reg == {$past(shift_reg[n-2:0]), $past(in)}
  );

  // Core functional check for temp_out/out update from pre-update shift_reg
  assert property (@(posedge clk) disable iff(!past_valid)
    out == (
      ( ($past(shift_reg[0]) != $past(shift_reg[n-1]))
      ||($past(shift_reg[0]) != $past(shift_reg[n-2]))
      ||($past(shift_reg[0]) != $past(shift_reg[n-3])) )
      ? 1'b0 : $past(shift_reg[n-1])
    )
  );

  // Liveness: sustained ones eventually produce out==1 (n+1 cycles)
  assert property (@(posedge clk) disable iff(!past_valid)
    in[* (n+1)] |-> out
  );

  // Coverage
  cover property (@(posedge clk) disable iff(!past_valid) $rose(out));
  cover property (@(posedge clk) disable iff(!past_valid) $fell(out));

  // Cover both decision branches of the core if/else
  cover property (@(posedge clk) disable iff(!past_valid)
    ( ($past(shift_reg[0]) != $past(shift_reg[n-1]))
     ||($past(shift_reg[0]) != $past(shift_reg[n-2]))
     ||($past(shift_reg[0]) != $past(shift_reg[n-3])) ) && !out
  );

  cover property (@(posedge clk) disable iff(!past_valid)
    ( ($past(shift_reg[0]) == $past(shift_reg[n-1]))
     &&($past(shift_reg[0]) == $past(shift_reg[n-2]))
     &&($past(shift_reg[0]) == $past(shift_reg[n-3]))
     && $past(shift_reg[n-1]) ) && out
  );

endmodule

// Example bind (place in a package or a TB file):
// bind glitch_filter glitch_filter_sva #(.n(n)) gf_sva (.*);