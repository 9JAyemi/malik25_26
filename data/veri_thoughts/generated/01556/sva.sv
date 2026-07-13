module IBUFCTRL_sva (
  input logic I,
  input logic IBUFDISABLE,
  input logic T,
  input logic O
);
  // No clock/reset in RTL; sample on any input edge.

  // O must equal the RTL combinational equation.
  check_mux_equation: assert property (
    @(posedge I or negedge I or posedge IBUFDISABLE or negedge IBUFDISABLE or posedge T or negedge T)
      O == (IBUFDISABLE ? (T ? 1'b0 : 1'b1) : I)
  );

  // When enabled (IBUFDISABLE==0), O follows I.
  check_enabled_path: assert property (
    @(posedge I or negedge I or posedge IBUFDISABLE or negedge IBUFDISABLE or posedge T or negedge T)
      (IBUFDISABLE == 1'b0) |-> (O == I)
  );

  // When disabled (IBUFDISABLE==1), O equals ~T.
  check_disabled_inverts_T: assert property (
    @(posedge I or negedge I or posedge IBUFDISABLE or negedge IBUFDISABLE or posedge T or negedge T)
      (IBUFDISABLE == 1'b1) |-> (O == ~T)
  );

  // Disabled and T=1 forces O=0.
  check_disabled_T1_drives_0: assert property (
    @(posedge I or negedge I or posedge IBUFDISABLE or negedge IBUFDISABLE or posedge T or negedge T)
      (IBUFDISABLE && T) |-> (O == 1'b0)
  );

  // Disabled and T=0 forces O=1.
  check_disabled_T0_drives_1: assert property (
    @(posedge I or negedge I or posedge IBUFDISABLE or negedge IBUFDISABLE or posedge T or negedge T)
      (IBUFDISABLE && !T) |-> (O == 1'b1)
  );
endmodule