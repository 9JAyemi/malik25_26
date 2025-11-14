// SVA checker for control_module
module control_module_sva (
  input  logic [3:0] input_1,
  input  logic [1:0] input_2,
  input  logic       input_3,
  input  logic       input_4,
  input  logic       input_5,
  input  logic       input_6,
  input  logic       input_7,
  input  logic       input_8,
  input  logic       output_1
);

  // drive a combinational sampling event
  event comb_ev;
  always @ (input_1 or input_2 or input_3 or input_4 or input_5 or input_6 or input_7 or input_8 or output_1) -> comb_ev;

  // 4-state functional model of the DUT's truth table (including truncation on input_2)
  function automatic logic exp_out(
    input logic [3:0] sel,
    input logic [1:0] in2,
    input logic       i3, i4, i5, i6, i7, i8
  );
    unique case (sel)
      4'd0   : exp_out = 1'b0;
      4'd1   : exp_out = i3;
      4'd2   : exp_out = i4;
      4'd3   : exp_out = i5;
      4'd4   : exp_out = i6;
      4'd5   : exp_out = i7;
      4'd6   : exp_out = i8;
      4'd7   : exp_out = in2[0]; // truncation is intentional
      default: exp_out = 1'b0;
    endcase
  endfunction

  // Core equivalence: DUT output matches the modeled truth table (4-state compare)
  property p_truth_table;
    @(comb_ev) 1'b1 |-> ##0 (output_1 === exp_out(input_1, input_2, input_3, input_4, input_5, input_6, input_7, input_8));
  endproperty
  a_truth_table: assert property (p_truth_table);

  // Robustness: when selecting case 7, MSB of input_2 must not affect output
  property p_in2_msb_no_effect;
    @(comb_ev) (input_1 == 4'd7 && $changed(input_2[1]) && $stable(input_2[0])) |-> ##0 $stable(output_1);
  endproperty
  a_in2_msb_no_effect: assert property (p_in2_msb_no_effect);

  // Coverage: hit all select values and default, and exercise case 7 details
  c_sel0     : cover property (@(comb_ev) input_1 == 4'd0);
  c_sel1     : cover property (@(comb_ev) input_1 == 4'd1);
  c_sel2     : cover property (@(comb_ev) input_1 == 4'd2);
  c_sel3     : cover property (@(comb_ev) input_1 == 4'd3);
  c_sel4     : cover property (@(comb_ev) input_1 == 4'd4);
  c_sel5     : cover property (@(comb_ev) input_1 == 4'd5);
  c_sel6     : cover property (@(comb_ev) input_1 == 4'd6);
  c_sel7     : cover property (@(comb_ev) input_1 == 4'd7);
  c_default  : cover property (@(comb_ev) input_1 inside {[4'd8:4'd15]});

  c_sel7_lsb0: cover property (@(comb_ev) input_1 == 4'd7 && input_2[0] == 1'b0);
  c_sel7_lsb1: cover property (@(comb_ev) input_1 == 4'd7 && input_2[0] == 1'b1);
  c_sel7_msb_toggle_no_out_change:
              cover property (@(comb_ev) input_1 == 4'd7 && $changed(input_2[1]) && $stable(input_2[0]) ##0 $stable(output_1));

endmodule

// Bind into the DUT
bind control_module control_module_sva u_control_module_sva (
  .input_1 (input_1),
  .input_2 (input_2),
  .input_3 (input_3),
  .input_4 (input_4),
  .input_5 (input_5),
  .input_6 (input_6),
  .input_7 (input_7),
  .input_8 (input_8),
  .output_1(output_1)
);