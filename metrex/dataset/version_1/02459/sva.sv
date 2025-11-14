// SVA checker for Delay_Block
module Delay_Block_sva #(
  parameter int DELAY = 2
) (
  input  logic                   clk,
  input  logic                   in,
  input  logic                   out,
  input  logic [DELAY-1:0]       delay_reg
);

  // Elaboration-time parameter sanity
  initial assert (DELAY >= 2)
    else $error("Delay_Block: parameter delay must be >= 2");

  // History guard so $past(..., DELAY) is valid
  logic [$clog2(DELAY+1)-1:0] hist;
  initial hist = '0;
  always_ff @(posedge clk) if (hist < DELAY) hist <= hist + 1;
  wire filled = (hist >= DELAY);

  default clocking cb @(posedge clk); endclocking

  // Functional spec: out equals input delayed by DELAY cycles
  assert property (filled |-> out == $past(in, DELAY));

  // Strong internal check: every pipeline bit matches the proper-aged input
  generate
    genvar k;
    for (k = 0; k < DELAY; k++) begin : g_map
      assert property (filled |-> delay_reg[k] == $past(in, k+1));
    end
  endgenerate

  // Structural tie-off: out is MSB of the shift register (after fill)
  assert property (filled |-> out == delay_reg[DELAY-1]);

  // Coverage: exercise rising/falling propagation through the delay
  cover property (filled && $rose(in) |-> ##DELAY $rose(out));
  cover property (filled && $fell(in) |-> ##DELAY $fell(out));
  cover property (filled && $changed(in) |-> ##DELAY $changed(out));

endmodule

// Bind the checker to all Delay_Block instances
bind Delay_Block Delay_Block_sva #(.DELAY(delay))
  Delay_Block_sva_i (.clk(clk), .in(in), .out(out), .delay_reg(delay_reg));