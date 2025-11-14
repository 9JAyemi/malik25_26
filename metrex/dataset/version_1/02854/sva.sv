// SVA checker for voltage_inverter
module voltage_inverter_sva (
  input logic A,
  input logic TE,
  input logic Z
);

  // Functional correctness (4-state exact): Z must equal A ^ TE at all times
  ap_func: assert property (Z === (A ^ TE))
    else $error("voltage_inverter SVA: Functional mismatch: Z !== A ^ TE");

  // Combinational zero-delay response on input changes
  ap_delta: assert property (@(posedge A or negedge A or posedge TE or negedge TE) ##0 (Z === (A ^ TE)))
    else $error("voltage_inverter SVA: Z not updated combinationally to A ^ TE");

  // When inputs are known, output must be known and correct
  ap_known: assert property ( (A inside {0,1} && TE inside {0,1}) |-> (Z inside {0,1} && Z == (A ^ TE)) )
    else $error("voltage_inverter SVA: Known inputs did not produce known/correct Z");

  // X/Z propagation: any unknown on inputs must yield unknown on Z
  ap_xprop: assert property ( ($isunknown(A) || $isunknown(TE)) |-> $isunknown(Z) )
    else $error("voltage_inverter SVA: X/Z on inputs not propagated to Z");


  // Coverage: all truth-table points observed
  cv_tt00: cover property (A==0 && TE==0 && Z==0);
  cv_tt01: cover property (A==0 && TE==1 && Z==1);
  cv_tt10: cover property (A==1 && TE==0 && Z==1);
  cv_tt11: cover property (A==1 && TE==1 && Z==0);

  // Coverage: data toggle behavior under both enables
  cv_a_follow:  cover property (@(posedge A or negedge A) (TE==0) ##0 (Z==A));
  cv_a_invert:  cover property (@(posedge A or negedge A) (TE==1) ##0 (Z==~A));

  // Coverage: TE toggle response with A held
  cv_te_resp:   cover property (@(posedge TE or negedge TE) ##0 (Z === (A ^ TE)));

endmodule

// Bind into the DUT
bind voltage_inverter voltage_inverter_sva u_voltage_inverter_sva (.A(A), .TE(TE), .Z(Z));