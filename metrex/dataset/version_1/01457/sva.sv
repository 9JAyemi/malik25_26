// SVA for four_bit_adder
module four_bit_adder_sva (
  input  logic        Clock,
  input  logic [3:0]  A,
  input  logic [3:0]  B,
  input  logic        Cin,
  input  logic [3:0]  Sum,
  input  logic        Cout
);

  default clocking cb @(posedge Clock); endclocking

  // Basic sanity: inputs/outputs known at sample points
  assert property ( !$isunknown({A,B,Cin}) );
  assert property ( !$isunknown({Sum,Cout}) );

  // Functional correctness: registered 5-bit sum of previous-cycle inputs
  assert property ( $past(1'b1) |-> {Cout,Sum} == ($past({1'b0,A}) + $past({1'b0,B}) + $past(Cin)) );

  // Carry-out matches threshold (redundant check, but clear)
  assert property ( $past(1'b1) |-> Cout == ( ($past(A) + $past(B) + $past(Cin)) >= 16 ) );

  // No glitches on registered outputs: they only change on rising edge
  assert property ( !$changed({Cout,Sum}) or $rose(Clock) );

  // Coverage: exercise carry/no-carry and extremes (sample after update with ##0)
  cover property ( @(posedge Clock) ##0 (Cout == 0) );
  cover property ( @(posedge Clock) ##0 (Cout == 1) );
  cover property ( @(posedge Clock) (A==4'h0 && B==4'h0 && Cin==1'b0) ##0 ({Cout,Sum} == 5'd0) );
  cover property ( @(posedge Clock) (A==4'hF && B==4'hF && Cin==1'b1) ##0 ({Cout,Sum} == 5'd31) );

  // Coverage: each Sum bit toggles across cycles
  genvar i;
  generate
    for (i=0; i<4; i++) begin : g_cov_toggle
      cover property ( @(posedge Clock) $past(1'b1) && (Sum[i] != $past(Sum[i])) );
    end
  endgenerate

endmodule

bind four_bit_adder four_bit_adder_sva sva_i (
  .Clock(Clock), .A(A), .B(B), .Cin(Cin), .Sum(Sum), .Cout(Cout)
);