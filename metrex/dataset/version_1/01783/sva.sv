// SVA bind file for top_module
module top_module_sva (
    input  logic [15:0] in,
    input  logic [2:0]  sel,
    input  logic [3:0]  data0, data1, data2, data3, data4, data5,
    input  logic [7:0]  out_hi,
    input  logic [7:0]  out_lo
);

  // Sample on any relevant signal change
  default clocking cb @(in or sel or data0 or data1 or data2 or data3 or data4 or data5 or out_hi or out_lo); endclocking

  // Helper: selected data (matches DUT mux behavior)
  let sel_data = (sel==3'd0) ? data0 :
                 (sel==3'd1) ? data1 :
                 (sel==3'd2) ? data2 :
                 (sel==3'd3) ? data3 :
                 (sel==3'd4) ? data4 : data5;

  // Functional correctness
  assert property (disable iff ($isunknown({in,out_lo}))
                   out_lo === (in[15:8] & in[7:0]));

  assert property (disable iff ($isunknown({sel,data0,data1,data2,data3,data4,data5,out_hi}))
                   out_hi === {4'h0, sel_data});

  // Minimal functional coverage
  cover property (sel==3'd0);
  cover property (sel==3'd1);
  cover property (sel==3'd2);
  cover property (sel==3'd3);
  cover property (sel==3'd4);
  cover property (sel inside {3'd5,3'd6,3'd7});

  cover property (! $isunknown(in) && ((in[15:8] & in[7:0]) == 8'h00));
  cover property (! $isunknown(in) && ((in[15:8] & in[7:0]) != 8'h00));

  cover property (! $isunknown({sel,data0,out_hi}) && sel==3'd0 && out_hi[3:0] == data0);
  cover property (! $isunknown({sel,data1,out_hi}) && sel==3'd1 && out_hi[3:0] == data1);
  cover property (! $isunknown({sel,data2,out_hi}) && sel==3'd2 && out_hi[3:0] == data2);
  cover property (! $isunknown({sel,data3,out_hi}) && sel==3'd3 && out_hi[3:0] == data3);
  cover property (! $isunknown({sel,data4,out_hi}) && sel==3'd4 && out_hi[3:0] == data4);
  cover property (! $isunknown({sel,data5,out_hi}) && (sel inside {3'd5,3'd6,3'd7}) && out_hi[3:0] == data5);

endmodule

// Bind into the DUT
bind top_module top_module_sva top_module_sva_i (.*);