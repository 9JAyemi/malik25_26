// SVA for top_module
// Bind this module: bind top_module top_module_sva sva();

module top_module_sva
(
  input logic        clk,
  input logic        reset,
  input logic [7:0]  a, b,
  input logic [7:0]  product,   // internal reg in DUT
  input logic [7:0]  quotient,  // internal reg in DUT
  input logic [7:0]  result
);

  default clocking cb @(posedge clk); endclocking

  // simple past-valid for up to 2-cycle history
  logic pv1, pv2;
  always_ff @(posedge clk) begin
    pv1 <= 1'b1;
    pv2 <= pv1;
  end

  // Reset behavior
  assert property (reset |=> (product==8'h00 && quotient==8'h00));
  assert property ((reset && $past(reset)) |-> (product==8'h00 && quotient==8'h00));

  // Product update (handles normal and reset-deassert cycle)
  assert property ((!reset && !$past(reset)) |-> product == ((($past(a)*$past(b)) & 16'h00FF)));
  assert property ((!reset &&  $past(reset)) |-> product == (((a*b) & 16'h00FF)));

  // Quotient update (handles normal and reset-deassert cycle)
  assert property ((!reset && !$past(reset)) |-> quotient == ($past(product) >> 1));
  assert property ((!reset &&  $past(reset)) |-> quotient == 8'h00);

  // Output wiring
  assert property (result == quotient);

  // End-to-end 2-cycle functional check (requires two consecutive non-reset cycles)
  assert property (pv2 && !reset && !$past(reset) |-> 
                   result == ( ((($past(a,2)*$past(b,2)) & 16'h00FF) >> 1) & 8'hFF) );

  // Coverage
  cover property (pv2 && $rose(reset));                             // reset seen
  cover property (pv2 && !$past(reset) && !reset);                  // at-speed operation
  cover property (pv2 && !reset && !$past(reset) &&                 // truncation/overflow exercised
                  (($past(a)*$past(b)) > 16'd255));
  cover property (pv2 && !reset && !$past(reset) &&                 // nonzero pipeline activity
                  (((($past(a)*$past(b)) & 16'h00FF) >> 1) & 8'hFF) == result && result!=8'h00);

endmodule

// Example bind (place in a package or separate file):
// bind top_module top_module_sva sva (.*);