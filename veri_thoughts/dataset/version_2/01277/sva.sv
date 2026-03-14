module mux_4to1_case_sva (
  input logic clk,              // external verification clock
  input logic [3:0] a,
  input logic [3:0] b,
  input logic [3:0] c,
  input logic [3:0] d,
  input logic [1:0] sel,
  input logic [3:0] out
);

  // When sel==00, out routes a.
  check_sel_00_routes_a: assert property (
    @(posedge clk) disable iff (1'b0) (sel === 2'b00) |-> (out == a)
  );

  // When sel==01, out routes b.
  check_sel_01_routes_b: assert property (
    @(posedge clk) disable iff (1'b0) (sel === 2'b01) |-> (out == b)
  );

  // When sel==10, out routes c.
  check_sel_10_routes_c: assert property (
    @(posedge clk) disable iff (1'b0) (sel === 2'b10) |-> (out == c)
  );

  // When sel==11, out routes d.
  check_sel_11_routes_d: assert property (
    @(posedge clk) disable iff (1'b0) (sel === 2'b11) |-> (out == d)
  );

  // If sel has X/Z, default branch drives zero.
  check_unknown_sel_routes_zero: assert property (
    @(posedge clk) disable iff (1'b0) $isunknown(sel) |-> (out == 4'b0000)
  );

  // For known sel, out equals the selected input.
  check_mapping_for_known_sel: assert property (
    @(posedge clk) disable iff (1'b0)
      (!$isunknown(sel)) |-> (
        ((sel === 2'b00) && (out == a)) ||
        ((sel === 2'b01) && (out == b)) ||
        ((sel === 2'b10) && (out == c)) ||
        ((sel === 2'b11) && (out == d))
      )
  );

  // If sel and selected input are stable, out is stable.
  check_out_stable_if_sel_and_selected_stable: assert property (
    @(posedge clk) disable iff (1'b0)
      ($stable(sel) &&
       (((sel === 2'b00) && $stable(a)) ||
        ((sel === 2'b01) && $stable(b)) ||
        ((sel === 2'b10) && $stable(c)) ||
        ((sel === 2'b11) && $stable(d))))) |-> $stable(out)
  );

  // Changes on unselected inputs do not affect out when sel==00 and a is stable.
  check_unselected_changes_ignore_out_sel00: assert property (
    @(posedge clk) disable iff (1'b0)
      ($stable(sel) && (sel === 2'b00) && $stable(a) && $changed({b,c,d})) |-> $stable(out)
  );

  // Changes on unselected inputs do not affect out when sel==01 and b is stable.
  check_unselected_changes_ignore_out_sel01: assert property (
    @(posedge clk) disable iff (1'b0)
      ($stable(sel) && (sel === 2'b01) && $stable(b) && $changed({a,c,d})) |-> $stable(out)
  );

  // Changes on unselected inputs do not affect out when sel==10 and c is stable.
  check_unselected_changes_ignore_out_sel10: assert property (
    @(posedge clk) disable iff (1'b0)
      ($stable(sel) && (sel === 2'b10) && $stable(c) && $changed({a,b,d})) |-> $stable(out)
  );

  // Changes on unselected inputs do not affect out when sel==11 and d is stable.
  check_unselected_changes_ignore_out_sel11: assert property (
    @(posedge clk) disable iff (1'b0)
      ($stable(sel) && (sel === 2'b11) && $stable(d) && $changed({a,b,c})) |-> $stable(out)
  );

endmodule