// SVA for mux4to1 (concise, quality-focused). Bind this to the DUT.

`ifndef MUX4TO1_SVA_SV
`define MUX4TO1_SVA_SV

module mux4to1_sva
(
  input logic [1:0] sel,
  input logic       data0, data1, data2, data3,
  input logic       out
);

  // Combinational sampling
  default clocking cb @(*) endclocking

  // Output must be known whenever inputs are known
  a_out_known_when_inputs_known: assert property
    (!$isunknown({sel,data0,data1,data2,data3})) |-> ##0 !$isunknown(out));

  // Functional correctness: 4:1 mux spec
  a_mux_func: assert property
    (!$isunknown({sel,data0,data1,data2,data3})) |-> ##0
      out == ((sel==2'b00) ? data0 :
              (sel==2'b01) ? data1 :
              (sel==2'b10) ? data2 : data3));

  // Pass-through when selected input toggles
  a_pass0: assert property
    (!$isunknown({sel,data0,out}) && sel==2'b00 && $changed(data0)) |-> ##0 out == data0);
  a_pass1: assert property
    (!$isunknown({sel,data1,out}) && sel==2'b01 && $changed(data1)) |-> ##0 out == data1);
  a_pass2: assert property
    (!$isunknown({sel,data2,out}) && sel==2'b10 && $changed(data2)) |-> ##0 out == data2);
  a_pass3: assert property
    (!$isunknown({sel,data3,out}) && sel==2'b11 && $changed(data3)) |-> ##0 out == data3);

  // Coverage: each select value exercised with correct mapping
  c_sel00: cover property (!$isunknown({sel,data0})) && sel==2'b00 && out==data0);
  c_sel01: cover property (!$isunknown({sel,data1})) && sel==2'b01 && out==data1);
  c_sel10: cover property (!$isunknown({sel,data2})) && sel==2'b10 && out==data2);
  c_sel11: cover property (!$isunknown({sel,data3})) && sel==2'b11 && out==data3);

  // Coverage: observe propagation when selected input changes
  c_pass0: cover property (sel==2'b00 && $changed(data0) ##0 $changed(out));
  c_pass1: cover property (sel==2'b01 && $changed(data1) ##0 $changed(out));
  c_pass2: cover property (sel==2'b10 && $changed(data2) ##0 $changed(out));
  c_pass3: cover property (sel==2'b11 && $changed(data3) ##0 $changed(out));

endmodule

// Bind into DUT (internal name connections use DUT ports)
bind mux4to1 mux4to1_sva
(
  .sel(sel),
  .data0(data0), .data1(data1), .data2(data2), .data3(data3),
  .out(out)
);

`endif