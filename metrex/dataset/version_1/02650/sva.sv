// SVA for decoder_4to16: active-low one-cold decoder
module decoder_4to16_sva (input logic [3:0] ABCD, input logic [15:0] Y);
  default clocking cb @(*); endclocking

  // Inputs should be known
  a_no_x_on_in: assert property (cb !$isunknown(ABCD));

  // Exact mapping: one bit cleared at index ABCD, others set
  a_map:       assert property (cb (!$isunknown(ABCD)) |-> (Y == ~(16'h1 << ABCD)));

  // One-cold check (exactly one 0)
  a_one_cold:  assert property (cb (!$isunknown(ABCD)) |-> $onehot(~Y));

  // Default path (all 1's) only if input is unknown
  a_def_only_on_x: assert property (cb (Y == 16'hFFFF) |-> $isunknown(ABCD));

  // Functional coverage: hit all 16 codes with correct mapping
  genvar i;
  generate for (i = 0; i < 16; i++) begin : gen_cov
    c_code: cover property (cb (ABCD == i) && (Y == ~(16'h1 << i)));
  end endgenerate

  // Optional: observe default on unknown input
  c_default_on_x: cover property (cb $isunknown(ABCD) && (Y == 16'hFFFF));
endmodule

bind decoder_4to16 decoder_4to16_sva u_decoder_4to16_sva(.ABCD(ABCD), .Y(Y));