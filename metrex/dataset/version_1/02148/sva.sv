// SVA for adder_module
// Binds a single-cycle reference model, key safety checks, and focused coverage.

module adder_module_sva (
  input logic        clk,
  input logic        rst,
  input logic [7:0]  A,
  input logic [7:0]  B,
  input logic [7:0]  R
);
  default clocking cb @(posedge clk); endclocking

  // Guard $past usage on first cycle
  logic past_valid; initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Golden reference: next R equals f(prev rst,A,B)
  assert property ( 1'b1 |=> R == ( $past(rst) ? 8'h00
                                              : ({1'b0,$past(A)} + {1'b0,$past(B)} + 9'd1)[7:0] ) );

  // While in reset (steady), R reads as 0
  assert property ( rst && $past(rst) |-> (R == 8'h00) );

  // No X/Z on output or inputs during active operation
  assert property ( disable iff (rst) !$isunknown(R) );
  assert property ( disable iff (rst) !$isunknown({A,B}) );

  // Coverage
  cover property ( rst |=> R == 8'h00 );                                 // reset clears
  cover property ( !rst && !$past(rst) && $past(A)==8'h00 && $past(B)==8'h00 |-> R==8'h01 ); // 0+0+1
  cover property ( !rst && !$past(rst) && $past(A)==8'hFF && $past(B)==8'h00 |-> R==8'h00 ); // wrap to 0
  cover property ( !rst && !$past(rst) && $past(A)==8'hFF && $past(B)==8'hFF |-> R==8'hFF ); // max result
  cover property ( $past(rst) && !rst |=> R == ({1'b0,A}+{1'b0,B}+9'd1)[7:0] );             // first add after reset
endmodule

bind adder_module adder_module_sva sva_i (.*);