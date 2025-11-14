// SVA checker for decoder. Bind this to the DUT.
// Focuses on pipeline timing, bit-ordering, width/zero-extension, and output mapping.

module decoder_sva (
  input logic        clk,
  input logic [3:0]  ABCD,
  input logic [15:0] out,
  input logic [15:0] stage1_out,
  input logic [15:0] stage2_out
);

  default clocking cb @(posedge clk); endclocking

  // Stage1 should capture zero-extended, specific bit-order inversion next cycle
  property p_stage1_load;
    1'b1 |=> stage1_out == {12'h000, ~ABCD[0], ~ABCD[1], ~ABCD[2], ~ABCD[3]};
  endproperty
  assert property (p_stage1_load);

  // Stage2 should capture bit-reversed stage1 value next cycle
  property p_stage2_reverse;
    1'b1 |=> stage2_out ==
      { stage1_out[0],  stage1_out[1],  stage1_out[2],  stage1_out[3],
        stage1_out[4],  stage1_out[5],  stage1_out[6],  stage1_out[7],
        stage1_out[8],  stage1_out[9],  stage1_out[10], stage1_out[11],
        stage1_out[12], stage1_out[13], stage1_out[14], stage1_out[15] };
  endproperty
  assert property (p_stage2_reverse);

  // Combinational relationship to output must always hold
  assert property (out == ~stage2_out);

  // End-to-end behavior: one-cycle latency, upper nibble mirrors ABCD, lower 12 bits are all 1s
  property p_end_to_end;
    1'b1 |=> (out[15:12] == ABCD) && (out[11:0] == 12'hFFF);
  endproperty
  assert property (p_end_to_end);

  // Concise functional coverage:
  // - See every ABCD value
  // - See end-to-end mapping for each ABCD value
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : gen_cov
      cover property (ABCD == i[3:0]);
      cover property ((ABCD == i[3:0]) |=> (out[15:12] == i[3:0]) && (out[11:0] == 12'hFFF));
    end
  endgenerate

endmodule

// Bind into DUT
bind decoder decoder_sva u_decoder_sva (
  .clk(clk),
  .ABCD(ABCD),
  .out(out),
  .stage1_out(stage1_out),
  .stage2_out(stage2_out)
);