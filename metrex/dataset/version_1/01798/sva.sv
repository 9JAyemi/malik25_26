// SVA for mux_4x1_w8
module mux_4x1_w8_sva #(parameter W=8)
(
  input  logic [1:0]   ctrl,
  input  logic [W-1:0] D0, D1, D2, D3,
  input  logic [W-1:0] S
);
  default clocking cb @($global_clock); endclocking

  // Functional correctness per select
  ap_sel00: assert property ( (ctrl == 2'b00) |-> ##0 (S == D0) );
  ap_sel01: assert property ( (ctrl == 2'b01) |-> ##0 (S == D1) );
  ap_sel10: assert property ( (ctrl == 2'b10) |-> ##0 (S == D2) );
  ap_sel11: assert property ( (ctrl == 2'b11) |-> ##0 (S == D3) );

  // No X on output when select/data are known
  ap_noX00: assert property ( (ctrl == 2'b00 && !$isunknown(D0)) |-> ##0 !$isunknown(S) );
  ap_noX01: assert property ( (ctrl == 2'b01 && !$isunknown(D1)) |-> ##0 !$isunknown(S) );
  ap_noX10: assert property ( (ctrl == 2'b10 && !$isunknown(D2)) |-> ##0 !$isunknown(S) );
  ap_noX11: assert property ( (ctrl == 2'b11 && !$isunknown(D3)) |-> ##0 !$isunknown(S) );

  // X-merge sanity: if ctrl is X/Z and all data equal, result equals that value
  ap_xmerge_all_equal: assert property (
    ($isunknown(ctrl) && (D0===D1) && (D1===D2) && (D2===D3)) |-> ##0 (S===D0)
  );

  // Stability: if all inputs stable, output is stable
  ap_stable: assert property ( $stable({ctrl,D0,D1,D2,D3}) |-> ##0 $stable(S) );

  // Minimal functional coverage
  cp_sel00: cover property ( (ctrl == 2'b00) && (S == D0) );
  cp_sel01: cover property ( (ctrl == 2'b01) && (S == D1) );
  cp_sel10: cover property ( (ctrl == 2'b10) && (S == D2) );
  cp_sel11: cover property ( (ctrl == 2'b11) && (S == D3) );
  cp_xmerge: cover property ( $isunknown(ctrl) && (D0===D1) && (D1===D2) && (D2===D3) && (S===D0) );
endmodule

bind mux_4x1_w8 mux_4x1_w8_sva i_mux_4x1_w8_sva (.ctrl(ctrl), .D0(D0), .D1(D1), .D2(D2), .D3(D3), .S(S));