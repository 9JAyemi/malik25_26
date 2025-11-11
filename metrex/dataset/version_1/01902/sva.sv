// SVA for delayN: concise, full functional/structural checks + key coverage

module delayN_sva #(parameter int unsigned NDELAY = 3)
(
  input logic clk,
  input logic in,
  input logic out
);
  // Access to DUT internals (shiftreg) via bind scope

  default clocking cb @(posedge clk); endclocking

  // Static param sanity
  initial assert (NDELAY >= 1) else $error("NDELAY must be >= 1");

  // Track when deep $past(...,NDELAY) is valid
  int unsigned cycles = 0;
  logic mature = 0;
  always_ff @(posedge clk) begin
    cycles <= cycles + 1;
    mature <= (cycles + 1 >= NDELAY);
  end

  // Out must equal MSB of shiftreg (combinational tie)
  assert property (out === shiftreg[NDELAY-1]);

  // Functional N-cycle delay
  assert property (disable iff (!mature) out == $past(in, NDELAY));

  // Structural shift behavior
  if (NDELAY >= 2) begin
    assert property (disable iff (cycles == 0)
                     shiftreg == { $past(shiftreg[NDELAY-2:0]), $past(in) });
  end else begin
    // For NDELAY == 1
    assert property (disable iff (cycles == 0) shiftreg[0] == $past(in));
  end

  // Coverage: both edges propagate through after N cycles; pipeline matures
  cover property ($rose(in) ##NDELAY $rose(out));
  cover property ($fell(in) ##NDELAY $fell(out));
  cover property (mature);

endmodule

bind delayN delayN_sva #(.NDELAY(NDELAY)) i_delayN_sva(.clk(clk), .in(in), .out(out));