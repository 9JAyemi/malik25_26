// SVA for the given design. Bind to top_module.
module top_module_sva (
    input  logic        CLK,
    input  logic        RESET,
    input  logic        LOAD,
    input  logic [3:0]  LOAD_VAL,
    input  logic [3:0]  A, B, C, D,
    input  logic [1:0]  S,
    input  logic [3:0]  Q,
    input  logic        Y, Z,
    input  logic        final_output
);
  // Clocking
  default clocking cb @(posedge CLK); endclocking

  // Helper for priority_mux S==2'b11 selected bit (LSB of first non-zero)
  function automatic logic sel11_bit;
    if (D != 4'b0) sel11_bit = D[0];
    else if (C != 4'b0) sel11_bit = C[0];
    else if (B != 4'b0) sel11_bit = B[0];
    else                 sel11_bit = A[0];
  endfunction

  // --------------------
  // counter assertions
  // --------------------

  // Asynchronous reset drives Q to 0 immediately
  property p_async_reset_q0;
    @(posedge RESET) ##0 (Q == 4'h0);
  endproperty
  assert property (p_async_reset_q0);

  // While RESET is asserted, Q must be 0
  assert property (RESET |-> (Q == 4'h0));

  // LOAD has priority: on LOAD, Q takes LOAD_VAL at the same cycle
  assert property (disable iff (RESET) LOAD |-> ##0 (Q == LOAD_VAL));

  // Increment when not RESET and not LOAD
  assert property (disable iff (RESET)
                   (!LOAD && $past(!RESET)) |-> (Q == (($past(Q)+4'd1) & 4'hF)));

  // Rollover from 0xF to 0x0 when incrementing
  assert property (disable iff (RESET)
                   ($past(!LOAD) && !LOAD && $past(Q)==4'hF) |-> (Q==4'h0));

  // Q must not be X/Z
  assert property (!$isunknown(Q));

  // --------------------
  // priority_mux assertions
  // --------------------

  // Exact decode for each S
  assert property ((S==2'b00) |-> (Y==1'b0 && Z==1'b0));
  assert property ((S==2'b01) |-> (Y==A[0]  && Z==~A[0]));
  assert property ((S==2'b10) |-> (Y==B[0]  && Z==~B[0]));
  assert property ((S==2'b11) |-> (Y==sel11_bit() && Z==~sel11_bit()));

  // For all non-00 selects, Z is complement of Y
  assert property ((S!=2'b00) |-> (Z==~Y));

  // Outputs must not be X/Z
  assert property (!$isunknown({Y,Z}));

  // --------------------
  // final_output assertions
  // --------------------

  // final_output definition
  assert property (final_output === (Q[0] && Y));

  // When S==00, Y==0 => final_output must be 0
  assert property ((S==2'b00) |-> (final_output==1'b0));

  // --------------------
  // Coverage
  // --------------------

  // Counter scenarios
  cover property (RESET ##1 !RESET ##1 (Q==4'h0) ##1 (Q==4'h1) ##1 (Q==4'h2));
  cover property (disable iff (RESET) LOAD);
  cover property (disable iff (RESET) LOAD ##1 LOAD); // back-to-back loads
  cover property (disable iff (RESET) $past(Q)==4'hF && !LOAD && Q==4'h0);

  // Mux select space and priority paths
  cover property (S==2'b00);
  cover property (S==2'b01);
  cover property (S==2'b10);
  cover property (S==2'b11 && (D!=0));
  cover property (S==2'b11 && (D==0) && (C!=0));
  cover property (S==2'b11 && (D==0) && (C==0) && (B!=0));
  cover property (S==2'b11 && (D==0) && (C==0) && (B==0)); // falls to A

  // final_output goes high
  cover property (final_output);

endmodule

bind top_module top_module_sva sva_top (
  .CLK(CLK), .RESET(RESET), .LOAD(LOAD), .LOAD_VAL(LOAD_VAL),
  .A(A), .B(B), .C(C), .D(D), .S(S),
  .Q(Q), .Y(Y), .Z(Z), .final_output(final_output)
);