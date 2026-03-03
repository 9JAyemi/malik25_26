// SVA checker for four_to_one_mux
module four_to_one_mux_sva (
  input logic        clk,        // sampling clock for temporal checks
  input logic [3:0]  in,
  input logic [1:0]  sel,
  input logic        out
);

  // Immediate (clockless) assertions: catch combinational mismatches ASAP
  always @* begin
    if (!$isunknown(sel)) begin
      assert (out === in[sel])
        else $error("MUX mismatch: sel=%0d out=%b in=%b", sel, out, in);
    end else begin
      assert (out === 1'b0)
        else $error("MUX default mismatch on unknown sel: out=%b", out);
    end
  end

  // Concurrent assertions for temporal behavior
  default clocking cb @(posedge clk); endclocking

  // Functional correctness each cycle
  property p_func_known;
    !$isunknown(sel) |-> (out === in[sel]);
  endproperty
  assert property (p_func_known);

  // Default behavior on X/Z select
  property p_func_unknown;
    $isunknown(sel) |-> (out === 1'b0);
  endproperty
  assert property (p_func_unknown);

  // Generate per-select propagation and isolation checks
  genvar i;
  for (i = 0; i < 4; i++) begin : gen_mux_checks
    // When selected input toggles and sel is stable/known, out follows in same cycle
    property p_follow_sel_i;
      $stable(sel) && (sel == i[1:0]) && !$isunknown(sel) && $changed(in[i])
        |-> ##0 (out === in[i]);
    endproperty
    assert property (p_follow_sel_i);

    // Changes on non-selected inputs must not affect out (with sel and selected input stable)
    property p_isolate_others_i;
      $stable(sel) && (sel == i[1:0]) && !$isunknown(sel) &&
      $stable(in[i]) && $changed(in) && !$changed(in[i])
        |-> ##0 $stable(out);
    endproperty
    assert property (p_isolate_others_i);

    // Coverage: see each select value
    cover property (sel == i[1:0]);

    // Coverage: observe propagation on selected input toggle
    cover property ($stable(sel) && (sel == i[1:0]) && !$isunknown(sel) &&
                    $changed(in[i]) ##0 (out === in[i]));
  end

  // Coverage: exercise unknown select case
  cover property ($isunknown(sel));

endmodule

// Bind into the DUT (adjust instance path or provide clk as appropriate)
// bind four_to_one_mux four_to_one_mux_sva sva_inst (.*);