// SVA bind module for adder_subtractor
module adder_subtractor_sva #(parameter WIDTH=4)
(
  input  logic [WIDTH-1:0] A,
  input  logic [WIDTH-1:0] B,
  input  logic             M,
  input  logic [WIDTH-1:0] Y
);

  // Sample on any input change; use ##0 to allow combinational settle
  default clocking cb @(A or B or M); endclocking

  // Functional correctness (mod 2^WIDTH): Y == A+B when M=0, Y == A-B when M=1
  property p_func;
    disable iff ($isunknown({A,B,M}))
    1'b1 |-> ##0 (Y == (M ? (A - B) : (A + B)));
  endproperty
  assert property (p_func);

  // Output must be known whenever inputs are known
  assert property ( (!$isunknown({A,B,M})) |-> ##0 (!$isunknown(Y)) );

  // Identities and corner sanity
  assert property ( disable iff($isunknown({A,B,M})) (B=={WIDTH{1'b0}}) |-> ##0 (Y==A) );
  assert property ( disable iff($isunknown({A,B,M})) (M && (A==B))     |-> ##0 (Y=={WIDTH{1'b0}}) );

  // Modular cancellation checks
  assert property ( disable iff($isunknown({A,B,M})) (!M) |-> ##0 (((Y - B) == A)) );
  assert property ( disable iff($isunknown({A,B,M})) ( M) |-> ##0 (((Y + B) == A)) );

  // Coverage: modes, overflow/underflow, edges, extremes
  cover property ( (!$isunknown({A,B})) && !M );                     // add mode seen
  cover property ( (!$isunknown({A,B})) &&  M );                     // sub mode seen
  cover property ( (!$isunknown({A,B})) && !M && ((A + B) < A) );    // add overflow (wrap)
  cover property ( (!$isunknown({A,B})) &&  M && (A < B) );          // sub underflow (wrap)
  cover property ( B=={WIDTH{1'b0}} );                               // B is zero
  cover property ( A=={WIDTH{1'b0}} );                               // A is zero
  cover property ( M && (A==B) );                                    // subtract to zero
  cover property ( (A=={WIDTH{1'b1}}) || (B=={WIDTH{1'b1}}) );       // max operand
  cover property ( @(posedge M) 1 );                                 // M rising edge
  cover property ( @(negedge M) 1 );                                 // M falling edge

endmodule

// Bind into the DUT
bind adder_subtractor adder_subtractor_sva #(.WIDTH(4)) u_adder_subtractor_sva (
  .A(A), .B(B), .M(M), .Y(Y)
);