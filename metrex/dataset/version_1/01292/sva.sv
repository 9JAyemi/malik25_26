// SVA for data_converter
// Bindable, concise, and focused on functional/coverage checks
module data_converter_sva (
  input clk,
  input reset,
  input [7:0]  in,
  input        select,
  input [15:0] out
);
  default clocking cb @(posedge clk); endclocking

  // Knownness
  ap_inputs_known: assert property (disable iff (reset) !$isunknown({in,select}));
  ap_out_known:    assert property (disable iff (reset) !$isunknown(out));

  // Reset behavior (synchronous): output is zero in the cycle reset is high
  ap_reset_zero:   assert property (reset |=> out == 16'h0000);

  // Core functionality
  ap_mapping:      assert property (disable iff (reset)
                                    out == (select ? {8'h00, in} : {in, 8'h00}));

  // Coverage
  cp_reset_deassert: cover property (reset ##1 !reset);
  cp_branch_sel0:    cover property (disable iff (reset)
                                     (!select && in != 8'h00 && out == {in, 8'h00}));
  cp_branch_sel1:    cover property (disable iff (reset)
                                     ( select && in != 8'h00 && out == {8'h00, in}));
  cp_sel_toggle:     cover property (disable iff (reset)
                                     (select ##1 !select) or (!select ##1 select));
endmodule

bind data_converter data_converter_sva u_data_converter_sva (
  .clk(clk), .reset(reset), .in(in), .select(select), .out(out)
);