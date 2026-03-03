// SVA for muxes. Bind these to the DUTs.
// Designed to be clockless and race-free via ##0 sampling on signal change.

package mux_sva_pkg;

  // 2:1 mux assertions and coverage
  module mux_2to1_sva #(parameter int W=8)
  (
    input logic [W-1:0] data0,
    input logic [W-1:0] data1,
    input logic         sel,
    input logic [W-1:0] out
  );

    // Select must not be X/Z
    a_no_x_sel: assert property (@(sel) !$isunknown(sel));

    // Functional equivalence (allowing X/Z on data/out via case equality), race-safe
    a_func: assert property (@(data0 or data1 or sel or out)
                               !$isunknown(sel) |-> ##0
                               (out === (sel ? data1 : data0)));

    // Redundant sanity: when sel is known, out equals one of the inputs
    a_member: assert property (@(data0 or data1 or sel or out)
                                 !$isunknown(sel) |-> ##0
                                 ((out === data0) || (out === data1)));

    // Coverage: see both sel values
    c_seen0: cover property (@(sel) sel == 1'b0);
    c_seen1: cover property (@(sel) sel == 1'b1);

    // Coverage: when each path is selected, input change propagates to out
    c_path0_prop: cover property (@(data0 or sel or out)
                                    (sel == 1'b0) && $changed(data0) |-> ##0 $changed(out));
    c_path1_prop: cover property (@(data1 or sel or out)
                                    (sel == 1'b1) && $changed(data1) |-> ##0 $changed(out));
  endmodule


  // 4:1 mux assertions and coverage
  module mux_4to1_using_2to1_sva #(parameter int W=8)
  (
    input logic [W-1:0] data0,
    input logic [W-1:0] data1,
    input logic [W-1:0] data2,
    input logic [W-1:0] data3,
    input logic [1:0]   sel,
    input logic [W-1:0] out
  );

    // Select must not be X/Z on any bit
    a_no_x_sel: assert property (@(sel) !$isunknown(sel));

    // Functional equivalence to hierarchical muxing, race-safe
    a_func: assert property (@(data0 or data1 or data2 or data3 or sel or out)
                               !$isunknown(sel) |-> ##0
                               (out === (sel[1] ? (sel[0] ? data3 : data2)
                                                : (sel[0] ? data1 : data0))));

    // Redundant sanity: when sel is known, out equals one of the inputs
    a_member: assert property (@(data0 or data1 or data2 or data3 or sel or out)
                                 !$isunknown(sel) |-> ##0
                                 ((out === data0) || (out === data1) || (out === data2) || (out === data3)));

    // Coverage: see all select values
    c_seen00: cover property (@(sel) sel == 2'b00);
    c_seen01: cover property (@(sel) sel == 2'b01);
    c_seen10: cover property (@(sel) sel == 2'b10);
    c_seen11: cover property (@(sel) sel == 2'b11);

    // Coverage: when each path is selected, input change propagates to out
    c_path00_prop: cover property (@(data0 or sel or out)
                                     (sel == 2'b00) && $changed(data0) |-> ##0 $changed(out));
    c_path01_prop: cover property (@(data1 or sel or out)
                                     (sel == 2'b01) && $changed(data1) |-> ##0 $changed(out));
    c_path10_prop: cover property (@(data2 or sel or out)
                                     (sel == 2'b10) && $changed(data2) |-> ##0 $changed(out));
    c_path11_prop: cover property (@(data3 or sel or out)
                                     (sel == 2'b11) && $changed(data3) |-> ##0 $changed(out));
  endmodule

endpackage


// Bind SVA to DUTs
import mux_sva_pkg::*;

bind mux_2to1               mux_2to1_sva               #(.W(8)) i_mux_2to1_sva               (.*);
bind mux_4to1_using_2to1    mux_4to1_using_2to1_sva    #(.W(8)) i_mux_4to1_using_2to1_sva    (.*);