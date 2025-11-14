// SVA for decoder. Bind this checker to the DUT and drive clk (and optional rst_n).
module decoder_sva #(parameter bit HAS_RSTN = 0)
(
  input logic        clk,
  input logic        rst_n,
  input logic [1:0]  SEL,
  input logic [15:0] OUT
);
  default clocking @(posedge clk); endclocking
  default disable iff (HAS_RSTN && !rst_n);

  // Sanity: no X/Z on key signals
  a_known_sel: assert property (!$isunknown(SEL));
  a_known_out: assert property (!$isunknown(OUT));

  // Functional mapping: OUT = 1 << SEL
  a_decode_eq: assert property (!$isunknown(SEL) |-> OUT == (16'h0001 << SEL));

  // Shape: exactly one of OUT[3:0] is 1 and upper bits are 0
  a_onehot4:   assert property (!$isunknown(OUT) |-> (OUT[15:4] == 12'h000 && $onehot(OUT[3:0])));

  // Stateless: if SEL is stable, OUT must be stable
  a_stateless: assert property ($stable(SEL) |-> $stable(OUT));

  // Coverage: hit all select/output pairs
  c_sel00: cover property (SEL == 2'b00 && OUT == 16'h0001);
  c_sel01: cover property (SEL == 2'b01 && OUT == 16'h0002);
  c_sel10: cover property (SEL == 2'b10 && OUT == 16'h0004);
  c_sel11: cover property (SEL == 2'b11 && OUT == 16'h0008);
endmodule

// Example bind (ensure clk/rst_n are in scope where decoder is instantiated)
// If no reset is available, tie rst_n to 1'b1 and keep HAS_RSTN=0.
bind decoder decoder_sva u_decoder_sva (.clk(clk), .rst_n(rst_n), .SEL(SEL), .OUT(OUT));