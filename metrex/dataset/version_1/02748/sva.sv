// SVA for mux4. Bind this to the DUT; no DUT/testbench edits needed.

module mux4_sva #(parameter WIDTH = 8)
(
  input  [WIDTH-1:0] d0, d1, d2, d3,
  input  [1:0]       sel,
  input  [WIDTH-1:0] y
);
  default clocking cb @(*); endclocking

  // Functional correctness (4-state aware, end-to-end)
  ap_func: assert property (
    y === (sel[1] ? (sel[0] ? d3 : d1) : (sel[0] ? d2 : d0))
  );

  // No-X on output when all inputs and select are fully known
  ap_known_out: assert property (
    !$isunknown({sel,d0,d1,d2,d3}) |-> !$isunknown(y)
  );

  // Per-select determinism when select is known
  ap_00: assert property ( (sel == 2'b00) |-> (y === d0) );
  ap_01: assert property ( (sel == 2'b01) |-> (y === d1) );
  ap_10: assert property ( (sel == 2'b10) |-> (y === d2) );
  ap_11: assert property ( (sel == 2'b11) |-> (y === d3) );

  // Coverage: exercise all select values
  cp_sel00: cover property ( sel == 2'b00 );
  cp_sel01: cover property ( sel == 2'b01 );
  cp_sel10: cover property ( sel == 2'b10 );
  cp_sel11: cover property ( sel == 2'b11 );

  // Coverage: observe each data path driving y with known values
  cp_path0: cover property ( (sel==2'b00) && !$isunknown(d0) && (y == d0) );
  cp_path1: cover property ( (sel==2'b01) && !$isunknown(d1) && (y == d1) );
  cp_path2: cover property ( (sel==2'b10) && !$isunknown(d2) && (y == d2) );
  cp_path3: cover property ( (sel==2'b11) && !$isunknown(d3) && (y == d3) );
endmodule

bind mux4 mux4_sva #(.WIDTH(WIDTH)) mux4_sva_b (.*);