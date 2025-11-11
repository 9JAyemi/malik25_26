// SVA for mux16x8 / mux16x4 / mux16x2
// Focus: correctness, X-propagation, causality, and selection coverage.
// Bind these to the DUT; no DUT changes required.

package mux_sva_pkg;

  function automatic logic [15:0] sel8(input logic [2:0] s,
                                       input logic [15:0] d0, d1, d2, d3, d4, d5, d6, d7);
    case (s)
      3'd0: sel8 = d0;
      3'd1: sel8 = d1;
      3'd2: sel8 = d2;
      3'd3: sel8 = d3;
      3'd4: sel8 = d4;
      3'd5: sel8 = d5;
      3'd6: sel8 = d6;
      3'd7: sel8 = d7;
      default: sel8 = 'x;
    endcase
  endfunction

  function automatic logic [15:0] sel4(input logic [1:0] s,
                                       input logic [15:0] d0, d1, d2, d3);
    case (s)
      2'd0: sel4 = d0;
      2'd1: sel4 = d1;
      2'd2: sel4 = d2;
      2'd3: sel4 = d3;
      default: sel4 = 'x;
    endcase
  endfunction

  function automatic logic [15:0] sel2(input logic s,
                                       input logic [15:0] d0, d1);
    case (s)
      1'b0: sel2 = d0;
      1'b1: sel2 = d1;
      default: sel2 = 'x;
    endcase
  endfunction

endpackage


// ---------------- mux16x8 SVA ----------------
module mux16x8_sva(
  input logic [15:0] data0, data1, data2, data3, data4, data5, data6, data7,
  input logic [2:0]  selectInput,
  input logic [15:0] out
);
  import mux_sva_pkg::*;

  // Select must be known (prevents latchy behavior on X/Z select)
  a_sel_known: assert property (@(selectInput) !$isunknown(selectInput))
    else $error("mux16x8: selectInput is X/Z");

  // Functional correctness: out equals selected data (post-delta to avoid races)
  a_func: assert property (@(data0 or data1 or data2 or data3 or data4 or data5 or data6 or data7 or selectInput)
                           ##0 (!$isunknown(selectInput) |-> (out === sel8(selectInput, data0, data1, data2, data3, data4, data5, data6, data7))))
    else $error("mux16x8: out != selected data");

  // No X/Z on out when select and selected input are known
  a_no_x: assert property (@(data0 or data1 or data2 or data3 or data4 or data5 or data6 or data7 or selectInput)
                           ##0 ((!$isunknown(selectInput) && !$isunknown(sel8(selectInput, data0, data1, data2, data3, data4, data5, data6, data7)))
                                |-> !$isunknown(out)))
    else $error("mux16x8: out has X/Z while selected input and select are known");

  // Causality: out changes only due to select change or currently selected data change
  a_causality: assert property (@(out) ##0
                                ($changed(out) |-> (
                                   $changed(selectInput) ||
                                   (selectInput==3'd0 && $changed(data0)) ||
                                   (selectInput==3'd1 && $changed(data1)) ||
                                   (selectInput==3'd2 && $changed(data2)) ||
                                   (selectInput==3'd3 && $changed(data3)) ||
                                   (selectInput==3'd4 && $changed(data4)) ||
                                   (selectInput==3'd5 && $changed(data5)) ||
                                   (selectInput==3'd6 && $changed(data6)) ||
                                   (selectInput==3'd7 && $changed(data7))
                                )))
    else $error("mux16x8: out changed without cause");

  // Coverage: hit each select value with correct output
  c_sel0: cover property (@(selectInput) ##0 (selectInput==3'd0 && out===data0));
  c_sel1: cover property (@(selectInput) ##0 (selectInput==3'd1 && out===data1));
  c_sel2: cover property (@(selectInput) ##0 (selectInput==3'd2 && out===data2));
  c_sel3: cover property (@(selectInput) ##0 (selectInput==3'd3 && out===data3));
  c_sel4: cover property (@(selectInput) ##0 (selectInput==3'd4 && out===data4));
  c_sel5: cover property (@(selectInput) ##0 (selectInput==3'd5 && out===data5));
  c_sel6: cover property (@(selectInput) ##0 (selectInput==3'd6 && out===data6));
  c_sel7: cover property (@(selectInput) ##0 (selectInput==3'd7 && out===data7));

endmodule


// ---------------- mux16x4 SVA ----------------
module mux16x4_sva(
  input logic [15:0] data0, data1, data2, data3,
  input logic [1:0]  selectInput,
  input logic [15:0] out
);
  import mux_sva_pkg::*;

  a_sel_known: assert property (@(selectInput) !$isunknown(selectInput))
    else $error("mux16x4: selectInput is X/Z");

  a_func: assert property (@(data0 or data1 or data2 or data3 or selectInput)
                           ##0 (!$isunknown(selectInput) |-> (out === sel4(selectInput, data0, data1, data2, data3))))
    else $error("mux16x4: out != selected data");

  a_no_x: assert property (@(data0 or data1 or data2 or data3 or selectInput)
                           ##0 ((!$isunknown(selectInput) && !$isunknown(sel4(selectInput, data0, data1, data2, data3)))
                                |-> !$isunknown(out)))
    else $error("mux16x4: out has X/Z while selected input and select are known");

  a_causality: assert property (@(out) ##0
                                ($changed(out) |-> (
                                   $changed(selectInput) ||
                                   (selectInput==2'd0 && $changed(data0)) ||
                                   (selectInput==2'd1 && $changed(data1)) ||
                                   (selectInput==2'd2 && $changed(data2)) ||
                                   (selectInput==2'd3 && $changed(data3))
                                )))
    else $error("mux16x4: out changed without cause");

  c_sel0: cover property (@(selectInput) ##0 (selectInput==2'd0 && out===data0));
  c_sel1: cover property (@(selectInput) ##0 (selectInput==2'd1 && out===data1));
  c_sel2: cover property (@(selectInput) ##0 (selectInput==2'd2 && out===data2));
  c_sel3: cover property (@(selectInput) ##0 (selectInput==2'd3 && out===data3));

endmodule


// ---------------- mux16x2 SVA ----------------
module mux16x2_sva(
  input logic [15:0] data0, data1,
  input logic        selectInput,
  input logic [15:0] out
);
  import mux_sva_pkg::*;

  a_sel_known: assert property (@(selectInput) !$isunknown(selectInput))
    else $error("mux16x2: selectInput is X/Z");

  a_func: assert property (@(data0 or data1 or selectInput)
                           ##0 (!$isunknown(selectInput) |-> (out === sel2(selectInput, data0, data1))))
    else $error("mux16x2: out != selected data");

  a_no_x: assert property (@(data0 or data1 or selectInput)
                           ##0 ((!$isunknown(selectInput) && !$isunknown(sel2(selectInput, data0, data1)))
                                |-> !$isunknown(out)))
    else $error("mux16x2: out has X/Z while selected input and select are known");

  a_causality: assert property (@(out) ##0
                                ($changed(out) |-> (
                                   $changed(selectInput) ||
                                   (selectInput==1'b0 && $changed(data0)) ||
                                   (selectInput==1'b1 && $changed(data1))
                                )))
    else $error("mux16x2: out changed without cause");

  c_sel0: cover property (@(selectInput) ##0 (selectInput==1'b0 && out===data0));
  c_sel1: cover property (@(selectInput) ##0 (selectInput==1'b1 && out===data1));

endmodule


// ---------------- Bind assertions to DUT ----------------
bind mux16x8 mux16x8_sva i_mux16x8_sva(
  .data0(data0), .data1(data1), .data2(data2), .data3(data3),
  .data4(data4), .data5(data5), .data6(data6), .data7(data7),
  .selectInput(selectInput), .out(out)
);

bind mux16x4 mux16x4_sva i_mux16x4_sva(
  .data0(data0), .data1(data1), .data2(data2), .data3(data3),
  .selectInput(selectInput), .out(out)
);

bind mux16x2 mux16x2_sva i_mux16x2_sva(
  .data0(data0), .data1(data1),
  .selectInput(selectInput), .out(out)
);