// Strong, concise SVA for decoder. Bind this to the DUT.

module decoder_sva (
  input logic        clk,
  input logic [3:0]  in,
  input logic [15:0] out,
  input logic [15:0] out_reg1,
  input logic [15:0] out_reg2,
  input logic [15:0] out_reg3,
  input logic [15:0] out_reg4
);

  default clocking cb @(posedge clk); endclocking

  // End-to-end functional correctness with 3-cycle latency
  property p_decode_3c;
    !$isunknown($past(in,3)) |-> out == (16'h1 << $past(in,3));
  endproperty
  assert property (p_decode_3c);

  // One-hot guarantee on the observable output once valid
  assert property (!$isunknown($past(in,3)) |-> $onehot(out));

  // Structural pipeline integrity
  assert property (out_reg3 == $past(out_reg2));
  assert property (out_reg4 == $past(out_reg3));

  // Out is driven solely by out_reg4
  assert property (@(*) out == out_reg4);

  // Combinational decode correctness and one-hotness
  assert property (@(*) !$isunknown(in) |-> (out_reg1 == (16'h1 << in) && $onehot(out_reg1)));

  // Out changes only on the active clock edge (no glitches between edges)
  assert property (@(negedge clk) $stable(out));

  // Functional coverage: exercise all 16 codes and observe correct bit after 3 cycles
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : COV
      cover property (in == i ##3 out[i]);
    end
  endgenerate

endmodule

bind decoder decoder_sva u_decoder_sva (
  .clk      (clk),
  .in       (in),
  .out      (out),
  .out_reg1 (out_reg1),
  .out_reg2 (out_reg2),
  .out_reg3 (out_reg3),
  .out_reg4 (out_reg4)
);