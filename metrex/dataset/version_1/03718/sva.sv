// SVA for gray_counter
// Bind this module to the DUT: bind gray_counter gray_counter_sva sva(.clk(clk), .rst(rst), .ena(ena), .q(q));

module gray_counter_sva #(parameter WIDTH=4) (
  input  logic                 clk,
  input  logic                 rst,   // active-low reset in DUT (rst==0 => reset asserted)
  input  logic                 ena,
  input  logic [WIDTH-1:0]     q
);

  // Helpers
  function automatic [WIDTH-1:0] gray_transform(input [WIDTH-1:0] v);
    return v ^ (v >> 1);
  endfunction
  localparam logic [WIDTH-1:0] ZERO = '0;
  localparam logic [WIDTH-1:0] ONE  = {{(WIDTH-1){1'b0}},1'b1};

  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset drives q to ZERO immediately at rst falling edge
  assert property (@(negedge rst) q == ZERO)
    else $error("q not ZERO on negedge rst");

  // While reset is asserted at a clock edge, q must be ZERO
  assert property (@cb !rst |-> q == ZERO)
    else $error("q not ZERO while rst low at clk edge");

  // No X/Z on q out of reset
  assert property (@cb rst |-> !$isunknown(q))
    else $error("q has X/Z when out of reset");

  // Functional updates (only when continuously out of reset)
  // ena == 1: q_next = q ^ (q>>1)
  assert property (@cb rst && $past(rst) && $past(ena)
                   |-> q == gray_transform($past(q)))
    else $error("Functional mismatch when ena==1");

  // ena == 0: q_next = q ^ (q>>1) ^ 1
  assert property (@cb rst && $past(rst) && !$past(ena)
                   |-> q == (gray_transform($past(q)) ^ ONE))
    else $error("Functional mismatch when ena==0");

  // Reset release behavior: previous cycle in reset implies past q was ZERO
  assert property (@cb $past(!rst) && rst |-> $past(q) == ZERO)
    else $error("q not ZERO in cycle prior to reset release");

  // First cycle after reset release updates from ZERO per ena
  assert property (@cb $past(!rst) && rst && ena |-> q == ZERO)
    else $error("Post-release update (ena==1) incorrect");
  assert property (@cb $past(!rst) && rst && !ena |-> q == ONE)
    else $error("Post-release update (ena==0) incorrect");

  // Coverage

  // Reset asserted and released
  cover property (@cb $fell(rst));
  cover property (@cb $rose(rst));

  // Exercise both functional branches with correct results
  cover property (@cb rst && $past(rst) && $past(ena)
                  && q == gray_transform($past(q)));
  cover property (@cb rst && $past(rst) && !$past(ena)
                  && q == (gray_transform($past(q)) ^ ONE));

  // Hit all possible q states while out of reset
  genvar i;
  generate
    for (i = 0; i < (1<<WIDTH); i++) begin : C_Q_STATES
      cover property (@cb rst && q == i[WIDTH-1:0]);
    end
  endgenerate

endmodule