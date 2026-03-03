// SVA for clock_generator
module clock_generator_sva(
  input logic        clk_in,
  input logic        clk_out,
  input logic [23:0] counter
);
  localparam int unsigned TCNT = 24'd4_999_999;
  localparam int unsigned N    = 5_000_000;

  default clocking cb @(posedge clk_in); endclocking
  bit past_valid = 0, aligned = 0;
  always @(posedge clk_in) begin
    past_valid <= 1'b1;
    if (past_valid && $past(counter)==TCNT && counter==0) aligned <= 1'b1; // observed a legal wrap
  end
  default disable iff (!past_valid || $isunknown({clk_out,counter}));

  // Output toggles only when terminal count was seen on previous cycle
  assert property ($changed(clk_out) |-> $past(counter)==TCNT);

  // After first legal wrap (aligned), enforce exact behavior
  assert property (disable iff (!aligned) (counter!=TCNT) |=> (counter==$past(counter)+1 && $stable(clk_out)));
  assert property (disable iff (!aligned) (counter==TCNT) |=> (counter==0 && $changed(clk_out)));
  assert property (disable iff (!aligned) counter <= TCNT);
  assert property (disable iff (!aligned) (counter==0) |-> $past(counter)==TCNT);

  // Exactly N input cycles between clk_out toggles
  sequence stable_n_minus_1; $stable(clk_out) [* (N-1)]; endsequence
  assert property (disable iff (!aligned) $changed(clk_out) |-> stable_n_minus_1 ##1 $changed(clk_out));

  // Coverage
  cover property ($changed(clk_out));                                                // saw a toggle
  cover property (aligned && (counter==TCNT) ##1 (counter==0 && $changed(clk_out))); // wrap+toggle
  cover property (aligned && $rose(clk_out) ##N $rose(clk_out));                     // period on rising edges
  cover property (aligned && $fell(clk_out) ##N $fell(clk_out));                     // period on falling edges
endmodule

bind clock_generator clock_generator_sva sva_i (.clk_in(clk_in), .clk_out(clk_out), .counter(counter));