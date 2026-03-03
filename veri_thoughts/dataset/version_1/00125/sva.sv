// SVA checker for s5: verifies full combinational mapping and collects coverage
module s5_sva(input logic [5:0] stage1_input,
              input logic [3:0] stage1_output);

  // Golden LUT for the S-box
  localparam logic [3:0] LUT [0:63] = '{
    4'd2,  4'd14, 4'd12, 4'd11, 4'd4,  4'd2,  4'd1,  4'd12,
    4'd7,  4'd4,  4'd10, 4'd7,  4'd11, 4'd13, 4'd6,  4'd1,
    4'd8,  4'd5,  4'd5,  4'd0,  4'd3,  4'd15, 4'd15, 4'd10,
    4'd13, 4'd3,  4'd0,  4'd9,  4'd14, 4'd8,  4'd9,  4'd6,
    4'd4,  4'd11, 4'd2,  4'd8,  4'd1,  4'd12, 4'd11, 4'd7,
    4'd10, 4'd1,  4'd13, 4'd14, 4'd7,  4'd2,  4'd8,  4'd13,
    4'd15, 4'd6,  4'd9,  4'd15, 4'd12, 4'd0,  4'd5,  4'd9,
    4'd6,  4'd10, 4'd3,  4'd4,  4'd0,  4'd5,  4'd14, 4'd3
  };

  // Combinational correctness and sanity checks
  always_comb begin
    assert (!$isunknown(stage1_input)) else
      $error("s5 SVA: X/Z on stage1_input");
    assert (!$isunknown(stage1_output)) else
      $error("s5 SVA: X/Z on stage1_output");
    assert (stage1_output == LUT[stage1_input]) else
      $error("s5 SVA: LUT mismatch: in=%0d exp=%0d got=%0d",
             stage1_input, LUT[stage1_input], stage1_output);
  end

  // Compact coverage: hit every legal input->output mapping observed
  genvar i;
  generate
    for (i = 0; i < 64; i++) begin : COV_I
      always @(stage1_input or stage1_output)
        cover (stage1_input == i && stage1_output == LUT[i]);
    end
  endgenerate

endmodule

// Bind into the DUT (adjust instance/path as needed)
bind s5 s5_sva s5_sva_u(.stage1_input(stage1_input),
                        .stage1_output(stage1_output));