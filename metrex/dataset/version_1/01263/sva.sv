// SVA for mux2_1
`ifndef MUX2_1_SVA_SV
`define MUX2_1_SVA_SV

module mux2_1_sva (
  input logic A,
  input logic B,
  input logic SEL,
  input logic VOUT,
  input logic VOUT_N
);

  // Core functional checks (as coded)
  assert property (@(A or B or SEL) VOUT   === (SEL ? B : A))
    else $error("VOUT mismatch: SEL=%0b A=%0b B=%0b VOUT=%0b", SEL, A, B, VOUT);

  assert property (@(A or B or SEL) VOUT_N === (SEL ? A : B)) // note: not ~VOUT
    else $error("VOUT_N mismatch: SEL=%0b A=%0b B=%0b VOUT_N=%0b", SEL, A, B, VOUT_N);

  // No X/Z on outputs when inputs and SEL are known
  assert property (@(A or B or SEL) (!$isunknown({SEL, A, B})) |-> (!$isunknown({VOUT, VOUT_N})))
    else $error("Unexpected X/Z on outputs with known inputs");

  // Swap behavior on SEL edges when A/B are stable
  assert property (@(posedge SEL)  $stable({A, B}) |-> (VOUT===B && VOUT_N===A))
    else $error("Bad swap on posedge SEL");

  assert property (@(negedge SEL)  $stable({A, B}) |-> (VOUT===A && VOUT_N===B))
    else $error("Bad swap on negedge SEL");

  // Minimal coverage
  cover property (@(posedge SEL));
  cover property (@(negedge SEL));
  cover property (@(A or B) (SEL==0) && (VOUT===A) && (VOUT_N===B));
  cover property (@(A or B) (SEL==1) && (VOUT===B) && (VOUT_N===A));

endmodule

bind mux2_1 mux2_1_sva u_mux2_1_sva (.*);

`endif