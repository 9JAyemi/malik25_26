// SVA for decoder: check correctness, one-hot, inverse mapping, and cover all codes.
module decoder_sva (
  input  logic [15:0] decoderout,
  input  logic [3:0]  waddr
);

  // Correct decode and no-X on output when waddr is known
  a_decode_eq: assert property (@(waddr or decoderout)
    !$isunknown(waddr) |-> (decoderout === (16'h0001 << waddr)));

  // One-hot guarantee when waddr is known
  a_onehot:    assert property (@(waddr or decoderout)
    !$isunknown(waddr) |-> $onehot(decoderout));

  // Inverse mapping: each bit implies its address
  genvar i;
  generate
    for (i=0; i<16; i++) begin : INV
      localparam logic [3:0] IDX = i[3:0];
      a_inv:   assert property (@(waddr or decoderout) decoderout[i] |-> (waddr == IDX));
      // Coverage: see each address and corresponding one-hot output
      c_hit:   cover  property (@(waddr or decoderout)
                   (waddr == IDX) && (decoderout == (16'h0001 << IDX)));
    end
  endgenerate

endmodule

// Bind to DUT
bind decoder decoder_sva u_decoder_sva (.decoderout(decoderout), .waddr(waddr));