// SVA checker for des_sbox6
// Bind example (provide your own clock/reset):
// bind des_sbox6 des_sbox6_sva u_sva(.clk(tb_clk), .rst_n(tb_rst_n), .right_xor_key_segment_din(right_xor_key_segment_din), .sbox_dout(sbox_dout));

module des_sbox6_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [0:5]  right_xor_key_segment_din,
  input  logic [0:3]  sbox_dout
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // DES S-Box 6 truth table (row 00,01,10,11; col 0..15)
  localparam logic [3:0] S6_LUT [0:63] = '{
    4'd12,4'd1,4'd10,4'd15,4'd9,4'd2,4'd6,4'd8,4'd0,4'd13,4'd3,4'd4,4'd14,4'd7,4'd5,4'd11,
    4'd10,4'd15,4'd4,4'd2,4'd7,4'd12,4'd9,4'd5,4'd6,4'd1,4'd13,4'd14,4'd0,4'd11,4'd3,4'd8,
    4'd9,4'd14,4'd15,4'd5,4'd2,4'd8,4'd12,4'd3,4'd7,4'd0,4'd4,4'd10,4'd1,4'd13,4'd11,4'd6,
    4'd4,4'd3,4'd2,4'd12,4'd9,4'd5,4'd15,4'd10,4'd11,4'd14,4'd1,4'd7,4'd6,4'd0,4'd8,4'd13
  };

  function automatic logic [5:0] idx6(input logic [0:5] din);
    idx6 = { {din[0], din[5]}, din[1:4] }; // idx = row(2b) :: col(4b)
  endfunction

  // Functional correctness (for fully known inputs)
  assert property (
    !$isunknown(right_xor_key_segment_din)
    |-> (sbox_dout == S6_LUT[idx6(right_xor_key_segment_din)])
  );

  // No X on output when input is known
  assert property (
    !$isunknown(right_xor_key_segment_din)
    |-> !$isunknown(sbox_dout)
  );

  // Functional coverage: hit all 64 input combinations
  genvar i;
  for (i = 0; i < 64; i++) begin : gen_cov_in
    cover property (right_xor_key_segment_din === i[5:0]);
  end

endmodule