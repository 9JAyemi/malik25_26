// SVA checker for output_select
module output_select_sva(
    input logic        sel,
    input logic [7:0]  out1,
    input logic [7:0]  out2,
    input logic [7:0]  out
);
  timeunit 1ns/1ps;

  // Core functional equivalence (also catches X on sel via ?: merge semantics)
  property p_core_func;
    @(sel or out1 or out2 or out)
      out == (sel ? out2 : out1);
  endproperty
  assert property (p_core_func)
    else $error("out must equal (sel ? out2 : out1)");

  // No spurious out change without input/control change
  property p_no_spurious_out_change;
    @(sel or out1 or out2 or out)
      $changed(out) |-> ($changed(sel) || $changed(out1) || $changed(out2));
  endproperty
  assert property (p_no_spurious_out_change)
    else $error("out changed without sel/out1/out2 change");

  // Zero-latency pass-through for both selections
  property p_zero_lat_sel0;
    @(out1 or sel)
      (sel === 1'b0 && $changed(out1)) |-> ##0 (out == out1);
  endproperty
  assert property (p_zero_lat_sel0)
    else $error("When sel==0, out must track out1 in same timestep");

  property p_zero_lat_sel1;
    @(out2 or sel)
      (sel === 1'b1 && $changed(out2)) |-> ##0 (out == out2);
  endproperty
  assert property (p_zero_lat_sel1)
    else $error("When sel==1, out must track out2 in same timestep");

  // Control must be known when data inputs differ
  property p_sel_known_when_diff;
    @(sel or out1 or out2)
      (out1 !== out2) |-> !$isunknown(sel);
  endproperty
  assert property (p_sel_known_when_diff)
    else $error("sel is X/Z while out1!=out2");

  // Coverage
  cover property (@(negedge sel) $stable(out1) && $stable(out2) ##0 (out == out1)); // select out1
  cover property (@(posedge sel) $stable(out1) && $stable(out2) ##0 (out == out2)); // select out2
  cover property (@(sel or out1 or out2) (sel==0 && out1!==out2 && out==out1));
  cover property (@(sel or out1 or out2) (sel==1 && out1!==out2 && out==out2));
endmodule

// Bind to DUT
bind output_select output_select_sva sva_output_select (.*);