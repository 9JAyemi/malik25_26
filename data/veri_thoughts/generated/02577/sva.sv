module mux_4_to_1_sva (
  input logic sel1,
  input logic sel2,
  input logic [3:0] d0,
  input logic [3:0] d1,
  input logic [3:0] d2,
  input logic [3:0] d3,
  input logic [3:0] out
);
  // Note: No clock/reset in RTL; sample assertions on posedge of sel1.

  // When sel1=1 and sel2=1, out must equal d3.
  check_sel11_routes_d3: assert property (
    @(posedge sel1) (sel1 && sel2) |-> (out == d3)
  );

  // When sel1=1 and sel2=0, out must equal d2.
  check_sel10_routes_d2: assert property (
    @(posedge sel1) (sel1 && !sel2) |-> (out == d2)
  );

  // When sel1=0 and sel2=1, out must equal d1.
  check_sel01_routes_d1: assert property (
    @(posedge sel1) (!sel1 && sel2) |-> (out == d1)
  );

  // When sel1=0 and sel2=0, out must equal d0.
  check_sel00_routes_d0: assert property (
    @(posedge sel1) (!sel1 && !sel2) |-> (out == d0)
  );

  // Out equals the exact ternary selection used in the RTL.
  check_mux_functional_equivalence: assert property (
    @(posedge sel1) out == ((sel1 & sel2) ? d3 :
                            (sel1 & ~sel2) ? d2 :
                            (~sel1 & sel2) ? d1 :
                            d0)
  );

  // Exactly one of the four selection minterms is true for any sel1/sel2.
  check_onehot_minterms: assert property (
    @(posedge sel1) $onehot({(sel1 & sel2), (sel1 & ~sel2), (~sel1 & sel2), (~sel1 & ~sel2)})
  );

endmodule