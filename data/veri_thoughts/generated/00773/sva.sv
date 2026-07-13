module mux4_sva #(
  parameter WIDTH = 32
) (
  input logic [1:0] sel,
  input logic [WIDTH-1:0] a,
  input logic [WIDTH-1:0] b,
  input logic [WIDTH-1:0] c,
  input logic [WIDTH-1:0] d,
  input logic [WIDTH-1:0] out
);
  ///// Combinational mux mapping /////
  // When sel==2'b00, out must equal a.
  check_sel_00_routes_a: assert property (
    @($global_clock) (sel == 2'b00) |-> (out == a)
  );
  // When sel==2'b01, out must equal b.
  check_sel_01_routes_b: assert property (
    @($global_clock) (sel == 2'b01) |-> (out == b)
  );
  // When sel==2'b10, out must equal c.
  check_sel_10_routes_c: assert property (
    @($global_clock) (sel == 2'b10) |-> (out == c)
  );
  // When sel==2'b11, out must equal d.
  check_sel_11_routes_d: assert property (
    @($global_clock) (sel == 2'b11) |-> (out == d)
  );

  ///// Stability properties /////
  // If sel and all data inputs are stable, out must be stable (no storage).
  check_no_spurious_change_when_all_stable: assert property (
    @($global_clock) $stable(sel) && $stable(a) && $stable(b) && $stable(c) && $stable(d) |-> $stable(out)
  );
  // If sel selects a and both sel and a are stable, out must be stable.
  check_stable_when_sel_00_and_a_stable: assert property (
    @($global_clock) (sel == 2'b00) && $stable(sel) && $stable(a) |-> $stable(out)
  );
  // If sel selects b and both sel and b are stable, out must be stable.
  check_stable_when_sel_01_and_b_stable: assert property (
    @($global_clock) (sel == 2'b01) && $stable(sel) && $stable(b) |-> $stable(out)
  );
  // If sel selects c and both sel and c are stable, out must be stable.
  check_stable_when_sel_10_and_c_stable: assert property (
    @($global_clock) (sel == 2'b10) && $stable(sel) && $stable(c) |-> $stable(out)
  );
  // If sel selects d and both sel and d are stable, out must be stable.
  check_stable_when_sel_11_and_d_stable: assert property (
    @($global_clock) (sel == 2'b11) && $stable(sel) && $stable(d) |-> $stable(out)
  );

endmodule