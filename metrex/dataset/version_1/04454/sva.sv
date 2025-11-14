// SVA for PE_ctrl — combinational decode and width checks with coverage.
// Clockless, event-driven sampling with ##0 to avoid race on combinational updates.

module pe_ctrl_sva(
  input  logic [10:0] ctrl,
  input  logic [3:0]  op,
  input  logic [31:0] width
);

  // Golden decode for op
  function automatic logic [3:0] op_ref (input logic [5:0] c);
    unique case (c)
      6'd0:  op_ref = 4'h0;
      6'd1:  op_ref = 4'h1;
      6'd2:  op_ref = 4'h2;
      6'd3:  op_ref = 4'h3;
      6'd4:  op_ref = 4'h4;
      6'd5:  op_ref = 4'h5;
      6'd6:  op_ref = 4'h6;
      6'd7:  op_ref = 4'h7;
      6'd8:  op_ref = 4'h8;
      6'd9:  op_ref = 4'h9;
      6'd10: op_ref = 4'hA;
      6'd11: op_ref = 4'hB;
      6'd12: op_ref = 4'hC;
      6'd13: op_ref = 4'hD;
      6'd14: op_ref = 4'hE;
      6'd15: op_ref = 4'hF;
      6'd16: op_ref = 4'hF;
      6'd17: op_ref = 4'h3;
      6'd18: op_ref = 4'h4;
      6'd19: op_ref = 4'hF;
      6'd20: op_ref = 4'h7;
      6'd21: op_ref = 4'h9;
      6'd22: op_ref = 4'hB;
      6'd23: op_ref = 4'hD;
      6'd24: op_ref = 4'h7;
      6'd25: op_ref = 4'h9;
      6'd26: op_ref = 4'hF;
      6'd27: op_ref = 4'h3;
      6'd28: op_ref = 4'h4;
      6'd29: op_ref = 4'hA;
      6'd30: op_ref = 4'hF;
      6'd31: op_ref = 4'hF;
      default: op_ref = 4'h0;
    endcase
  endfunction

  // Decode correctness (combinational)
  property p_op_decode;
    @(ctrl) ##0 (op == op_ref(ctrl[5:0]));
  endproperty
  assert property (p_op_decode)
    else $error("PE_ctrl: op decode mismatch for ctrl=%b op=%b exp=%b",
                ctrl, op, op_ref(ctrl[5:0]));

  // Width correctness = 2**ctrl[10:6] and exactly one-hot
  property p_width_val;
    @(ctrl) ##0 (width == (32'h1 << ctrl[10:6]) && $onehot(width));
  endproperty
  assert property (p_width_val)
    else $error("PE_ctrl: width mismatch or not one-hot for ctrl[10:6]=%0d width=0x%08h",
                ctrl[10:6], width);

  // No X/Z on outputs when inputs are known
  property p_no_x_when_known_in;
    @(ctrl or op or width) ##0 (!$isunknown(ctrl) |-> (!$isunknown(op) && !$isunknown(width)));
  endproperty
  assert property (p_no_x_when_known_in)
    else $error("PE_ctrl: X/Z on outputs while ctrl is known");

  // Coverage: hit each enumerated case item and the default bucket
  genvar i;
  generate
    for (i = 0; i < 32; i++) begin : C_DECODES
      cover property (@(ctrl) ##0 (ctrl[5:0] == i[5:0]));
    end
  endgenerate
  cover property (@(ctrl) ##0 (ctrl[5:0] inside {[6'd32:6'd63]})); // default branch taken

  // Coverage: exponent extremes
  cover property (@(ctrl) ##0 (ctrl[10:6] == 5'd0));
  cover property (@(ctrl) ##0 (ctrl[10:6] == 5'd31));

endmodule

// Example bind (connect to the instance's ports; no clock needed):
// bind PE_ctrl pe_ctrl_sva pe_ctrl_sva_i(.ctrl(ctrl), .op(op), .width(width));