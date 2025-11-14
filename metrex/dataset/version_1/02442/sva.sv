// SVA for clock_control
// Focused, concise checks and covers. Bind into DUT.

module clock_control_sva (
  input  logic        inclk,
  input  logic        ena,
  input  logic        outclk,
  input  logic [1:0]  state,
  input  logic        filtered_clk
);

  // sampling guard
  logic past_valid;
  always_ff @(posedge inclk) past_valid <= 1'b1;

  default clocking cb @(posedge inclk); endclocking
  default disable iff (!past_valid);

  // Structural equivalence
  assert property (outclk == filtered_clk);

  // State behavior
  assert property (!ena |=> state == $past(state));                      // hold when disabled
  assert property ( ena |=> state == { $past(state[0]), 1'b1 });         // shift in '1' (since sampling at posedge inclk)

  // Filtered clock behavior
  assert property (!ena |=> filtered_clk == 1'b0);                       // force low when disabled
  assert property ( ena && state==2'b01 |=> filtered_clk == 1'b1);       // rise pattern
  assert property ( ena && state==2'b10 |=> filtered_clk == 1'b0);       // fall pattern
  assert property ( ena && state!=2'b01 && state!=2'b10
                    |=> filtered_clk == $past(filtered_clk));            // otherwise hold

  // Filtered clock may only change for legal reasons
  assert property ( (filtered_clk != $past(filtered_clk)) |->
                    ( (!$past(ena) && filtered_clk==1'b0) ||
                      ($past(ena) && $past(state)==2'b01 && filtered_clk==1'b1) ||
                      ($past(ena) && $past(state)==2'b10 && filtered_clk==1'b0) ) );

  // Coverage
  cover property ( ena && state==2'b01 ##1 filtered_clk==1'b1 );         // rising detect used
  cover property ( ena && state==2'b10 ##1 filtered_clk==0 );            // falling detect used (likely unreachable)
  cover property ( !ena ##1 filtered_clk==0 );                           // disable forces low
  cover property ( $rose(filtered_clk) );
  cover property ( $fell(filtered_clk) );
  cover property ( state==2'b10 );                                       // highlight potential unreachable state
endmodule

bind clock_control clock_control_sva i_clock_control_sva (.*);