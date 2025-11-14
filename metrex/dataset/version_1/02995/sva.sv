// SVA for mux4to1
// Concise, focuses on functional correctness, X checks, and coverage.
// Bind to DUT at bottom.

module mux4to1_sva (
  input logic [7:0] data0,
  input logic [7:0] data1,
  input logic [7:0] data2,
  input logic [7:0] data3,
  input logic       sel0,
  input logic       sel1,
  input logic [7:0] out
);

  // Abbreviation for the selected data
  function automatic logic [7:0] sel_data();
    sel_data = sel1 ? (sel0 ? data3 : data2) : (sel0 ? data1 : data0);
  endfunction

  // 1) Functional correctness (use === to allow X-equivalence); ##0 to avoid race with comb update
  assert property (@(data0 or data1 or data2 or data3 or sel0 or sel1)
                   ##0 (out === sel_data()))
    else $error("mux4to1: out != selected data");

  // 2) Control must be known (no X/Z on selects)
  assert property (@(sel0 or sel1) ##0 !$isunknown({sel1, sel0}))
    else $error("mux4to1: select has X/Z");

  // 3) If control and selected data are known, out must be known
  assert property (@(data0 or data1 or data2 or data3 or sel0 or sel1)
                   (! $isunknown({sel1,sel0}) && ! $isunknown(sel_data())) |-> ##0 ! $isunknown(out))
    else $error("mux4to1: out has X/Z while control and selected data are known");

  // 4) Propagation: if select is stable and selected input changes, out updates immediately
  assert property (@(data0 or sel0 or sel1)
                   ($stable({sel1,sel0}) && {sel1,sel0}==2'b00 && $changed(data0)) |-> ##0 (out === data0))
    else $error("mux4to1: data0 change not reflected at out");
  assert property (@(data1 or sel0 or sel1)
                   ($stable({sel1,sel0}) && {sel1,sel0}==2'b01 && $changed(data1)) |-> ##0 (out === data1))
    else $error("mux4to1: data1 change not reflected at out");
  assert property (@(data2 or sel0 or sel1)
                   ($stable({sel1,sel0}) && {sel1,sel0}==2'b10 && $changed(data2)) |-> ##0 (out === data2))
    else $error("mux4to1: data2 change not reflected at out");
  assert property (@(data3 or sel0 or sel1)
                   ($stable({sel1,sel0}) && {sel1,sel0}==2'b11 && $changed(data3)) |-> ##0 (out === data3))
    else $error("mux4to1: data3 change not reflected at out");

  // Coverage: hit all select combinations
  cover property (@(sel0 or sel1) {sel1,sel0}==2'b00);
  cover property (@(sel0 or sel1) {sel1,sel0}==2'b01);
  cover property (@(sel0 or sel1) {sel1,sel0}==2'b10);
  cover property (@(sel0 or sel1) {sel1,sel0}==2'b11);

  // Coverage: observe propagation for each selected input
  cover property (@(data0 or sel0 or sel1) ({sel1,sel0}==2'b00 && $changed(data0)) ##0 (out === data0));
  cover property (@(data1 or sel0 or sel1) ({sel1,sel0}==2'b01 && $changed(data1)) ##0 (out === data1));
  cover property (@(data2 or sel0 or sel1) ({sel1,sel0}==2'b10 && $changed(data2)) ##0 (out === data2));
  cover property (@(data3 or sel0 or sel1) ({sel1,sel0}==2'b11 && $changed(data3)) ##0 (out === data3));

endmodule

bind mux4to1 mux4to1_sva mux4to1_sva_i (.*);