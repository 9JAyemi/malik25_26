// SVA for MISTRAL_* LUT/NOT/ARITH cells.
// Concise functional checks + essential coverage.
// Drop this in a separate file and compile with the DUT.
// If you prefer bind, keep the binds at the end; they pass the DUT parameters.

`ifndef MISTRAL_SVA
`define MISTRAL_SVA

// -------------------- ALUT6 --------------------
module MISTRAL_ALUT6_sva #(parameter [63:0] LUT_P = 64'h0)
(
  input logic A,B,C,D,E,F,
  input logic Q
);
  // Functional check against parameter table (1-hot bit select)
  property p_lut6;
    @(A or B or C or D or E or F or Q)
      !$isunknown({A,B,C,D,E,F}) |-> (Q === LUT_P[{F,E,D,C,B,A}]);
  endproperty
  a_lut6: assert property(p_lut6);

  // Minimal activity coverage
  cover property (@(posedge A) 1);
  cover property (@(negedge A) 1);
  cover property (@(posedge B) 1);
  cover property (@(negedge B) 1);
  cover property (@(posedge C) 1);
  cover property (@(negedge C) 1);
  cover property (@(posedge D) 1);
  cover property (@(negedge D) 1);
  cover property (@(posedge E) 1);
  cover property (@(negedge E) 1);
  cover property (@(posedge F) 1);
  cover property (@(negedge F) 1);
  cover property (@(posedge Q) 1);
  cover property (@(negedge Q) 1);
endmodule

// -------------------- ALUT5 --------------------
module MISTRAL_ALUT5_sva #(parameter [31:0] LUT_P = 32'h0)
(
  input logic A,B,C,D,E,
  input logic Q
);
  property p_lut5;
    @(A or B or C or D or E or Q)
      !$isunknown({A,B,C,D,E}) |-> (Q === LUT_P[{E,D,C,B,A}]);
  endproperty
  a_lut5: assert property(p_lut5);

  cover property (@(posedge A) 1); cover property (@(negedge A) 1);
  cover property (@(posedge B) 1); cover property (@(negedge B) 1);
  cover property (@(posedge C) 1); cover property (@(negedge C) 1);
  cover property (@(posedge D) 1); cover property (@(negedge D) 1);
  cover property (@(posedge E) 1); cover property (@(negedge E) 1);
  cover property (@(posedge Q) 1); cover property (@(negedge Q) 1);
endmodule

// -------------------- ALUT4 --------------------
module MISTRAL_ALUT4_sva #(parameter [15:0] LUT_P = 16'h0)
(
  input logic A,B,C,D,
  input logic Q
);
  property p_lut4;
    @(A or B or C or D or Q)
      !$isunknown({A,B,C,D}) |-> (Q === LUT_P[{D,C,B,A}]);
  endproperty
  a_lut4: assert property(p_lut4);

  cover property (@(posedge A) 1); cover property (@(negedge A) 1);
  cover property (@(posedge B) 1); cover property (@(negedge B) 1);
  cover property (@(posedge C) 1); cover property (@(negedge C) 1);
  cover property (@(posedge D) 1); cover property (@(negedge D) 1);
  cover property (@(posedge Q) 1); cover property (@(negedge Q) 1);
endmodule

// -------------------- ALUT3 --------------------
module MISTRAL_ALUT3_sva #(parameter [7:0] LUT_P = 8'h0)
(
  input logic A,B,C,
  input logic Q
);
  property p_lut3;
    @(A or B or C or Q)
      !$isunknown({A,B,C}) |-> (Q === LUT_P[{C,B,A}]);
  endproperty
  a_lut3: assert property(p_lut3);

  cover property (@(posedge A) 1); cover property (@(negedge A) 1);
  cover property (@(posedge B) 1); cover property (@(negedge B) 1);
  cover property (@(posedge C) 1); cover property (@(negedge C) 1);
  cover property (@(posedge Q) 1); cover property (@(negedge Q) 1);
endmodule

// -------------------- ALUT2 --------------------
module MISTRAL_ALUT2_sva #(parameter [3:0] LUT_P = 4'h0)
(
  input logic A,B,
  input logic Q
);
  property p_lut2;
    @(A or B or Q)
      !$isunknown({A,B}) |-> (Q === LUT_P[{B,A}]);
  endproperty
  a_lut2: assert property(p_lut2);

  cover property (@(posedge A) 1); cover property (@(negedge A) 1);
  cover property (@(posedge B) 1); cover property (@(negedge B) 1);
  cover property (@(posedge Q) 1); cover property (@(negedge Q) 1);
endmodule

// -------------------- NOT --------------------
module MISTRAL_NOT_sva;
  // Bind by ports to avoid name collisions across instances
  // Define as an interface-style checker using bind-time connections
  // Dummy ports are inferred in bind.
  // Assertion and coverage are event-driven on A/Q
  property p_not(input logic A, Q);
    @(A or Q) !$isunknown(A) |-> (Q === ~A);
  endproperty
  // no static ports here; see bind connections for A/Q
endmodule

// -------------------- ALUT_ARITH --------------------
module MISTRAL_ALUT_ARITH_sva #(parameter [15:0] LUT0_P = 16'h0,
                                parameter [15:0] LUT1_P = 16'h0)
(
  input logic A,B,C,D0,D1,CI,
  input logic SO,CO
);
  // Local lets for clarity
  let idx0 = {D0,C,B,A};
  let idx1 = {D1,C,B,A};
  let q0   = LUT0_P[idx0];
  let n_q1 = ~LUT1_P[idx1];

  // SO = XOR of 3 inputs; CO = majority of 3 inputs
  property p_arith;
    @(A or B or C or D0 or D1 or CI or SO or CO)
      !$isunknown({A,B,C,D0,D1,CI})
      |-> (SO === (q0 ^ n_q1 ^ CI))
          && (CO === ((q0 & n_q1) | (q0 & CI) | (n_q1 & CI)));
  endproperty
  a_arith: assert property(p_arith);

  // Minimal output space coverage
  cover property (@(A or B or C or D0 or D1 or CI) {CO,SO}==2'b00);
  cover property (@(A or B or C or D0 or D1 or CI) {CO,SO}==2'b01);
  cover property (@(A or B or C or D0 or D1 or CI) {CO,SO}==2'b10);
  cover property (@(A or B or C or D0 or D1 or CI) {CO,SO}==2'b11);
  cover property (@(posedge CI) 1);
  cover property (@(negedge CI) 1);
endmodule

// -------------------- Binds --------------------
// These binds pass the DUT parameters into the SVA modules.
// Place these at top-level after compiling the DUT, or inside a package included after the DUT.
// Note: Some tools require the bind to be visible where DUT parameters are visible.
// If needed, move the bind statements into the corresponding DUT module bodies.

bind MISTRAL_ALUT6
  MISTRAL_ALUT6_sva #(.LUT_P(LUT))
  MISTRAL_ALUT6_sva_i (.A(A),.B(B),.C(C),.D(D),.E(E),.F(F),.Q(Q));

bind MISTRAL_ALUT5
  MISTRAL_ALUT5_sva #(.LUT_P(LUT))
  MISTRAL_ALUT5_sva_i (.A(A),.B(B),.C(C),.D(D),.E(E),.Q(Q));

bind MISTRAL_ALUT4
  MISTRAL_ALUT4_sva #(.LUT_P(LUT))
  MISTRAL_ALUT4_sva_i (.A(A),.B(B),.C(C),.D(D),.Q(Q));

bind MISTRAL_ALUT3
  MISTRAL_ALUT3_sva #(.LUT_P(LUT))
  MISTRAL_ALUT3_sva_i (.A(A),.B(B),.C(C),.Q(Q));

bind MISTRAL_ALUT2
  MISTRAL_ALUT2_sva #(.LUT_P(LUT))
  MISTRAL_ALUT2_sva_i (.A(A),.B(B),.Q(Q));

// For NOT, bind with port connections directly
bind MISTRAL_NOT
  assert property (MISTRAL_NOT_sva::p_not(A,Q));

bind MISTRAL_ALUT_ARITH
  MISTRAL_ALUT_ARITH_sva #(.LUT0_P(LUT0), .LUT1_P(LUT1))
  MISTRAL_ALUT_ARITH_sva_i (.A(A),.B(B),.C(C),.D0(D0),.D1(D1),.CI(CI),.SO(SO),.CO(CO));

`endif // MISTRAL_SVA