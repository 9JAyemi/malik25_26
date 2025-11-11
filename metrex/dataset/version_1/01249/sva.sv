// SVA for mux_comp
module mux_comp_sva(
  input logic [63:0] in,
  input logic [3:0]  sel,
  input logic [3:0]  comp_val,
  input logic [3:0]  selected_input, // internal reg via bind
  input logic        out
);

  // Helper to compute the selected nibble per spec
  function automatic logic [3:0] nibble_sel(input logic [63:0] din, input logic [3:0] s);
    case (s)
      4'd0:  nibble_sel = din[3:0];
      4'd1:  nibble_sel = din[7:4];
      4'd2:  nibble_sel = din[11:8];
      4'd3:  nibble_sel = din[15:12];
      4'd4:  nibble_sel = din[19:16];
      4'd5:  nibble_sel = din[23:20];
      4'd6:  nibble_sel = din[27:24];
      4'd7:  nibble_sel = din[31:28];
      4'd8:  nibble_sel = din[35:32];
      4'd9:  nibble_sel = din[39:36];
      4'd10: nibble_sel = din[43:40];
      4'd11: nibble_sel = din[47:44];
      4'd12: nibble_sel = din[51:48];
      4'd13: nibble_sel = din[55:52];
      4'd14: nibble_sel = din[59:56];
      4'd15: nibble_sel = din[63:60];
      default: nibble_sel = 4'hx;
    endcase
  endfunction

  // Basic 2-state sanity
  assert property (@(sel) !$isunknown(sel)) else $error("sel has X/Z");
  assert property (@(out) !$isunknown(out)) else $error("out has X/Z");

  // Selected-input must match the correct nibble when sel is known
  assert property (@(in or sel) !$isunknown(sel) |-> selected_input == nibble_sel(in, sel))
    else $error("selected_input mismatch");

  // Out must be the equality of selected_input and comp_val
  assert property (@(selected_input or comp_val) out == (selected_input == comp_val))
    else $error("out != (selected_input == comp_val)");

  // Out must also match direct compare of the selected nibble (bypassing internal reg)
  assert property (@(in or sel or comp_val) !$isunknown(sel) |-> out == (nibble_sel(in, sel) == comp_val))
    else $error("out != (nibble_sel(in,sel) == comp_val)");

  // No X on selected_input when sel and the selected nibble are known
  assert property (@(in or sel) (!$isunknown(sel) && !$isunknown(nibble_sel(in,sel))) |-> !$isunknown(selected_input))
    else $error("selected_input has X/Z under known inputs");

  // Coverage: exercise all sel values and both out polarities
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : COV_SEL
      cover property (@(sel) sel == i[3:0]);
    end
  endgenerate
  cover property (@(in or sel or comp_val) (nibble_sel(in,sel) == comp_val)); // out should be 1
  cover property (@(in or sel or comp_val) (nibble_sel(in,sel) != comp_val)); // out should be 0

endmodule

// Bind into DUT (connects to internal selected_input by name)
bind mux_comp mux_comp_sva sva_mux_comp (.*);