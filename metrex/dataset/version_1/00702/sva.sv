// SVA checker for Mux8
module Mux8_sva #(parameter Size = 8)
(
  input  wire [2:0]       select,
  input  wire [Size-1:0]  data_i00,
  input  wire [Size-1:0]  data_i01,
  input  wire [Size-1:0]  data_i02,
  input  wire [Size-1:0]  data_i03,
  input  wire [Size-1:0]  data_i04,
  input  wire [Size-1:0]  data_i05,
  input  wire [Size-1:0]  data_i06,
  input  wire [Size-1:0]  data_i07,
  input  wire [Size-1:0]  data_o
);

  // Helper: expected data for a 2-state select; 'x for X/Z select
  function automatic [Size-1:0] exp_data (input [2:0] sel);
    case (sel)
      3'd0: exp_data = data_i00;
      3'd1: exp_data = data_i01;
      3'd2: exp_data = data_i02;
      3'd3: exp_data = data_i03;
      3'd4: exp_data = data_i04;
      3'd5: exp_data = data_i05;
      3'd6: exp_data = data_i06;
      3'd7: exp_data = data_i07;
      default: exp_data = 'x;
    endcase
  endfunction

  // Select must never be X/Z to avoid latch-like behavior
  property p_select_known;
    @(select) !$isunknown(select);
  endproperty
  assert property (p_select_known)
    else $error("Mux8 SVA: select contains X/Z (latch risk)");

  // Functional correctness when selected input is known
  property p_mux_func_known;
    @(select or data_i00 or data_i01 or data_i02 or data_i03
      or data_i04 or data_i05 or data_i06 or data_i07 or data_o)
      (!$isunknown(select) && !$isunknown(exp_data(select)))
      |-> ##0 (data_o == exp_data(select));
  endproperty
  assert property (p_mux_func_known)
    else $error("Mux8 SVA: data_o != selected input (known case)");

  // X/Z propagation: when selected input has X/Z, output must match bit-for-bit
  property p_mux_xprop;
    @(select or data_i00 or data_i01 or data_i02 or data_i03
      or data_i04 or data_i05 or data_i06 or data_i07 or data_o)
      (!$isunknown(select) && $isunknown(exp_data(select)))
      |-> ##0 (data_o === exp_data(select));
  endproperty
  assert property (p_mux_xprop)
    else $error("Mux8 SVA: data_o does not match X/Z of selected input");

  // Basic functional coverage: hit all select values
  cover property (@(select) select == 3'd0);
  cover property (@(select) select == 3'd1);
  cover property (@(select) select == 3'd2);
  cover property (@(select) select == 3'd3);
  cover property (@(select) select == 3'd4);
  cover property (@(select) select == 3'd5);
  cover property (@(select) select == 3'd6);
  cover property (@(select) select == 3'd7);

endmodule

// Bind the checker to the DUT
bind Mux8 Mux8_sva #(.Size(Size)) Mux8_sva_i (
  .select(select),
  .data_i00(data_i00),
  .data_i01(data_i01),
  .data_i02(data_i02),
  .data_i03(data_i03),
  .data_i04(data_i04),
  .data_i05(data_i05),
  .data_i06(data_i06),
  .data_i07(data_i07),
  .data_o(data_o)
);