// SVA for mux_2to1_enable
// Bindable, concise, checks functional correctness, control integrity, and combinational behavior, with focused coverage.

module mux_2to1_enable_sva #(parameter WIDTH=8)
(
  input logic        enable,
  input logic [7:0]  in1,
  input logic [7:0]  in2,
  input logic [7:0]  out
);

  // Sample on any relevant signal change; ##0 used to check post-combinational settle
  default clocking cb @(in1 or in2 or enable or out); endclocking

  // Control must be known (avoid X/Z on control)
  a_enable_known: assert property ( !$isunknown(enable) );

  // Functional correctness (selected path)
  a_sel0: assert property ( (enable===1'b0) |-> ##0 (out===in1) );
  a_sel1: assert property ( (enable===1'b1) |-> ##0 (out===in2) );

  // Out changes only due to selected input or control change
  a_out_change_has_cause: assert property (
    $changed(out) |-> ( $changed(enable)
                      || ((enable===1'b0) && $changed(in1))
                      || ((enable===1'b1) && $changed(in2)) )
  );

  // Unselected input must not affect out
  a_unselected_in2_no_effect: assert property (
    (enable===1'b0 && $changed(in2) && $stable(in1) && $stable(enable)) |-> ##0 $stable(out)
  );
  a_unselected_in1_no_effect: assert property (
    (enable===1'b1 && $changed(in1) && $stable(in2) && $stable(enable)) |-> ##0 $stable(out)
  );

  // Immediate check for continuous combinational relation
  always @* begin
    if (enable === 1'b0) assert (out === in1);
    else if (enable === 1'b1) assert (out === in2);
  end

  // Coverage: both paths, enable toggles, and data propagation on selected path
  c_path0:   cover property ( (enable===1'b0 && in1!=in2) ##0 (out===in1) );
  c_path1:   cover property ( (enable===1'b1 && in1!=in2) ##0 (out===in2) );
  c_en_0to1: cover property ( enable===1'b0 ##1 enable===1'b1 );
  c_en_1to0: cover property ( enable===1'b1 ##1 enable===1'b0 );
  c_data0:   cover property ( (enable===1'b0 && $changed(in1)) ##0 $changed(out) );
  c_data1:   cover property ( (enable===1'b1 && $changed(in2)) ##0 $changed(out) );

endmodule

// Bind into the DUT
bind mux_2to1_enable mux_2to1_enable_sva #(.WIDTH(8)) mux_2to1_enable_sva_i (.*);