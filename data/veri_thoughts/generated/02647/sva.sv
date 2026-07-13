module mux4x1_sva (
  input logic S0,
  input logic S1,
  input logic A,
  input logic B,
  input logic C,
  input logic D,
  input logic Y
);
  // No clock or reset in RTL; pure combinational 4:1 mux selecting A/B/C/D by {S1,S0}.
  // Sample on any input edge to evaluate combinational behavior.

  // When S1=1 and S0=1, Y must equal D.
  check_sel_11_routes_D: assert property (
    @(posedge S0 or negedge S0 or posedge S1 or negedge S1 or posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
      (S1 && S0) |-> (Y == D)
  );

  // When S1=1 and S0=0, Y must equal C.
  check_sel_10_routes_C: assert property (
    @(posedge S0 or negedge S0 or posedge S1 or negedge S1 or posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
      (S1 && !S0) |-> (Y == C)
  );

  // When S1=0 and S0=1, Y must equal B.
  check_sel_01_routes_B: assert property (
    @(posedge S0 or negedge S0 or posedge S1 or negedge S1 or posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
      (!S1 && S0) |-> (Y == B)
  );

  // When S1=0 and S0=0, Y must equal A.
  check_sel_00_routes_A: assert property (
    @(posedge S0 or negedge S0 or posedge S1 or negedge S1 or posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
      (!S1 && !S0) |-> (Y == A)
  );

  // Y equals the mux function of selects and data inputs.
  check_mux_function_equivalence: assert property (
    @(posedge S0 or negedge S0 or posedge S1 or negedge S1 or posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
      Y == ((S1 & S0) ? D :
            (S1 & ~S0) ? C :
            (~S1 & S0) ? B :
                         A)
  );

endmodule