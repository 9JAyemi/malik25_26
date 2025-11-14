// SVA for mux_2to1
module mux_2to1_sva (input logic out, in0, in1, sel);

  // Sample on any change of relevant signals
  clocking cb @(posedge in0 or negedge in0
                or posedge in1 or negedge in1
                or posedge sel or negedge sel
                or posedge out or negedge out);
  endclocking
  default clocking cb;

  // Functional correctness for known select
  a_sel0: assert property ( (sel === 1'b0) |-> ##0 (out === in0) )
    else $error("mux_2to1: sel==0 but out != in0");
  a_sel1: assert property ( (sel === 1'b1) |-> ##0 (out === in1) )
    else $error("mux_2to1: sel==1 but out != in1");

  // Equal inputs force out regardless of sel (covers X/Z sel too)
  a_equal_inputs: assert property ( (in0 === in1) |-> ##0 (out === in0) )
    else $error("mux_2to1: in0==in1 but out differs");

  // X/Z on select resolves per ?: rules
  a_selx_xprop: assert property (
      $isunknown(sel) |-> ##0 ( (in0 === in1) ? (out === in0) : $isunknown(out) )
  ) else $error("mux_2to1: X/Z sel resolution incorrect");

  // Output only changes if an input or sel changed
  a_change_caused: assert property (
      $changed(out) |-> ($changed(in0) || $changed(in1) || $changed(sel))
  ) else $error("mux_2to1: out changed without cause");

  // Selected input change propagates; unselected input change does not
  a_prop_sel0:    assert property ( (sel === 1'b0 && $changed(in0)) |-> ##0 ($changed(out) && (out === in0)) );
  a_no_prop_sel0: assert property ( (sel === 1'b0 && $changed(in1) && !$changed(sel)) |-> ##0 !$changed(out) );
  a_prop_sel1:    assert property ( (sel === 1'b1 && $changed(in1)) |-> ##0 ($changed(out) && (out === in1)) );
  a_no_prop_sel1: assert property ( (sel === 1'b1 && $changed(in0) && !$changed(sel)) |-> ##0 !$changed(out) );

  // Coverage
  c_path0:             cover property ( (sel === 1'b0) ##0 (out === in0) );
  c_path1:             cover property ( (sel === 1'b1) ##0 (out === in1) );
  c_selx_diff_inputs:  cover property ( $isunknown(sel) && (in0 !== in1) ##0 $isunknown(out) );
  c_out_toggles:       cover property ( $changed(out) );

endmodule

bind mux_2to1 mux_2to1_sva i_mux_2to1_sva (.out(out), .in0(in0), .in1(in1), .sel(sel));