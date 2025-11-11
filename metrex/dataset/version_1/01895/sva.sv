// SVA for the given design (bind-ready). Assumes a testbench clock "clk".
// Import and reuse small reference functions for conciseness and consistency.

package pe_addsub_sva_pkg;
  // Reference model for priority_encoder.Q
  function automatic logic [1:0] pe_ref (
    input logic [3:0] A, B, C, D,
    input logic       S1, S0
  );
    logic [1:0] s;
    unique case ({S1,S0})
      2'b00: s = (A>B && A>C && A>D) ? 2'd0 :
               (B>C && B>D)          ? 2'd1 :
               (C>D)                 ? 2'd2 :
                                        2'd3;
      2'b01: s = (B>A && B>C && B>D) ? 2'd0 :
               (A>C && A>D)          ? 2'd1 :
               (C>D)                 ? 2'd2 :
                                        2'd3;
      2'b10: s = (C>A && C>B && C>D) ? 2'd0 :
               (A>B && A>D)          ? 2'd1 :
               (B>D)                 ? 2'd2 :
                                        2'd3;
      default: // 2'b11
               s = (D>A && D>B && D>C) ? 2'd0 :
               (A>B && A>C)            ? 2'd1 :
               (B>C)                   ? 2'd2 :
                                          2'd3;
    endcase
    return s;
  endfunction

  // 5-bit adder for correct sum/carry checking
  function automatic logic [4:0] add5 (
    input logic [3:0] A, B,
    input logic       Cn
  );
    return {1'b0,A} + {1'b0,B} + Cn;
  endfunction
endpackage


// ---------------- priority_encoder SVA ----------------
module priority_encoder_sva (
  input logic       clk,
  input logic [3:0] A, B, C, D,
  input logic       S1, S0,
  input logic [1:0] Q
);
  import pe_addsub_sva_pkg::*;

  // No X/Z on observed signals
  assert property (@(posedge clk) !$isunknown({A,B,C,D,S1,S0,Q}))
    else $error("priority_encoder: X/Z detected on inputs/outputs");

  // Functional equivalence to spec
  assert property (@(posedge clk) Q == pe_ref(A,B,C,D,S1,S0))
    else $error("priority_encoder: Q mismatch vs reference");

  // Minimal but meaningful coverage
  // - exercise all select values
  cover property (@(posedge clk) {S1,S0}==2'b00);
  cover property (@(posedge clk) {S1,S0}==2'b01);
  cover property (@(posedge clk) {S1,S0}==2'b10);
  cover property (@(posedge clk) {S1,S0}==2'b11);

  // - exercise all Q outcomes
  cover property (@(posedge clk) Q==2'd0);
  cover property (@(posedge clk) Q==2'd1);
  cover property (@(posedge clk) Q==2'd2);
  cover property (@(posedge clk) Q==2'd3);

  // - tie-case coverage showing intended priority behavior (example)
  cover property (@(posedge clk)
                  {S1,S0}==2'b00 && (A==B) && (A>C) && (A>D) && Q==2'd1);
endmodule

// ---------------- adder_subtractor SVA ----------------
module adder_subtractor_sva (
  input logic       clk,
  input logic [3:0] A, B,
  input logic       Cn,
  input logic       Sub,
  input logic [3:0] S,
  input logic       Cout
);
  import pe_addsub_sva_pkg::*;

  // No X/Z on observed signals
  assert property (@(posedge clk) !$isunknown({A,B,Cn,Sub,S,Cout}))
    else $error("adder_subtractor: X/Z detected on inputs/outputs");

  // Addition mode: exact 5-bit result split into S and Cout
  assert property (@(posedge clk)
                   !Sub |-> (S==add5(A,B,Cn)[3:0] && Cout==add5(A,B,Cn)[4]))
    else $error("adder_subtractor: add mode mismatch");

  // Subtraction mode: 4-bit wrap on S, no-borrow flag on Cout
  assert property (@(posedge clk)
                   Sub |-> (S==(A-B) && Cout==(A>=B)))
    else $error("adder_subtractor: sub mode mismatch");

  // Coverage: carry/no-carry and borrow/no-borrow
  cover property (@(posedge clk) (!Sub) && add5(A,B,Cn)[4]);
  cover property (@(posedge clk) (!Sub) && !add5(A,B,Cn)[4]);
  cover property (@(posedge clk) ( Sub) && (A<B));   // borrow
  cover property (@(posedge clk) ( Sub) && (A>=B));  // no borrow
endmodule

// ---------------- top_module SVA ----------------
module top_module_sva (
  input logic       clk,
  input logic [3:0] A, B, C, D,
  input logic       S1, S0,
  input logic [1:0] encoded_input
);
  import pe_addsub_sva_pkg::*;

  // No X/Z on observed signals
  assert property (@(posedge clk) !$isunknown({A,B,C,D,S1,S0,encoded_input}))
    else $error("top_module: X/Z detected on inputs/outputs");

  // top_module behavior: encoded_input == {1'b0, pe_ref(A,B,C,D,S1,S0)[1]}
  // (since assignment zero-extends the 1-bit expression)
  logic [1:0] pe_q;
  always_comb pe_q = pe_ref(A,B,C,D,S1,S0);

  assert property (@(posedge clk) encoded_input == {1'b0, pe_q[1]})
    else $error("top_module: encoded_input mapping mismatch");

  // Also explicitly assert MSB is always 0 per implementation
  assert property (@(posedge clk) encoded_input[1] == 1'b0)
    else $error("top_module: encoded_input[1] must be 0");

  // Coverage: both encoded outcomes exercised
  cover property (@(posedge clk) (pe_q[1]==1'b1) && (encoded_input==2'b01));
  cover property (@(posedge clk) (pe_q[1]==1'b0) && (encoded_input==2'b00));
endmodule


// ---------------- Example binds (adjust clk as appropriate) ----------------
// bind priority_encoder  priority_encoder_sva  pe_sva_i   (.clk(clk), .A(A), .B(B), .C(C), .D(D), .S1(S1), .S0(S0), .Q(Q));
// bind adder_subtractor  adder_subtractor_sva  addsub_i   (.clk(clk), .A(A), .B(B), .Cn(Cn), .Sub(Sub), .S(S), .Cout(Cout));
// bind top_module        top_module_sva        top_sva_i  (.clk(clk), .A(A), .B(B), .C(C), .D(D), .S1(S1), .S0(S0), .encoded_input(encoded_input));