// SVA for mux4x1: concise, functional, and coverage-focused
module mux4x1_sva (
  input  logic [7:0] data0, data1, data2, data3,
  input  logic [1:0] selectInput,
  input  logic [7:0] out
);
  // Sample on any relevant activity; use ##0 in consequents to avoid delta races
  default clocking cb @(data0 or data1 or data2 or data3 or selectInput or out); endclocking

  // Sanity: select must be 2-state (avoid X/Z driving incomplete case)
  a_select_known: assert property (!$isunknown(selectInput));

  // Functional mapping (overlapped implication with ##0 for combinational settle)
  a_sel0: assert property (selectInput == 2'b00 |-> ##0 (out === data0));
  a_sel1: assert property (selectInput == 2'b01 |-> ##0 (out === data1));
  a_sel2: assert property (selectInput == 2'b10 |-> ##0 (out === data2));
  a_sel3: assert property (selectInput == 2'b11 |-> ##0 (out === data3));

  // Functional coverage: hit each select path with correct output
  c_sel0: cover property (selectInput == 2'b00 ##0 (out === data0));
  c_sel1: cover property (selectInput == 2'b01 ##0 (out === data1));
  c_sel2: cover property (selectInput == 2'b10 ##0 (out === data2));
  c_sel3: cover property (selectInput == 2'b11 ##0 (out === data3));

  // Coverage: exercise select changes
  c_sel_change: cover property ($changed(selectInput));

  // Coverage: observe propagation on the selected path when input toggles
  c_prop0: cover property ((selectInput == 2'b00 && $changed(data0)) ##0 (out === data0));
  c_prop1: cover property ((selectInput == 2'b01 && $changed(data1)) ##0 (out === data1));
  c_prop2: cover property ((selectInput == 2'b10 && $changed(data2)) ##0 (out === data2));
  c_prop3: cover property ((selectInput == 2'b11 && $changed(data3)) ##0 (out === data3));
endmodule

// Bind to DUT
bind mux4x1 mux4x1_sva u_mux4x1_sva (
  .data0(data0), .data1(data1), .data2(data2), .data3(data3),
  .selectInput(selectInput), .out(out)
);