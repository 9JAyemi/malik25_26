// SVA for Multiplier
// Bind into the DUT: bind Multiplier Multiplier_sva sva();

module Multiplier_sva (
  input logic        clk,
  input logic        rst,
  input logic        load_i,
  input logic [31:0] Data_A_i,
  input logic [31:0] Data_B_i,
  input logic [63:0] sgf_result_o
);

  default clocking cb @(posedge clk); endclocking

  // Synchronous reset behavior
  property p_sync_reset_clears;
    rst |=> (sgf_result_o == 64'd0);
  endproperty
  assert property (p_sync_reset_clears);

  // Update on load with correct 32x32->64 product
  property p_load_updates_with_product;
    disable iff (rst)
      load_i |=> (sgf_result_o == $past($unsigned(Data_A_i) * $unsigned(Data_B_i)));
  endproperty
  assert property (p_load_updates_with_product);

  // Hold when not loading
  property p_hold_when_noload;
    disable iff (rst)
      !load_i |=> (sgf_result_o == $past(sgf_result_o));
  endproperty
  assert property (p_hold_when_noload);

  // Output changes only due to load or reset
  property p_change_requires_load_or_reset;
    disable iff (rst)
      (sgf_result_o != $past(sgf_result_o)) |-> $past(load_i);
  endproperty
  assert property (p_change_requires_load_or_reset);

  // No X/Z on critical signals
  property p_no_x_on_inputs_when_loading;
    disable iff (rst)
      load_i |-> (!$isunknown(Data_A_i) && !$isunknown(Data_B_i));
  endproperty
  assert property (p_no_x_on_inputs_when_loading);

  property p_no_x_on_output_when_active;
    disable iff (rst)
      !$isunknown(sgf_result_o);
  endproperty
  assert property (p_no_x_on_output_when_active);

  // Minimal but meaningful functional coverage
  cover property (rst);
  cover property (load_i && (Data_A_i == 32'd0 || Data_B_i == 32'd0));
  cover property (load_i && (Data_A_i == 32'hFFFF_FFFF) && (Data_B_i == 32'hFFFF_FFFF));
  cover property (load_i &&
                  (|Data_A_i[15:0]) && (|Data_A_i[31:16]) &&
                  (|Data_B_i[15:0]) && (|Data_B_i[31:16])); // excites all partial products

endmodule