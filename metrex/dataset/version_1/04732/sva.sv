// SVA for top_module and its internal decoders.
// Bind this module to top_module and drive clk/rst_n from your TB.

module top_module_sva
(
  input  logic        clk,
  input  logic        rst_n,
  // DUT ports
  input  logic [15:0] in,
  input  logic [1:0]  en1,
  input  logic        en2,
  input  logic [7:0]  out_hi,
  input  logic [7:0]  out_lo,
  // DUT internals
  input  logic [3:0]  dec1_out,
  input  logic [15:0] dec2_out,
  input  logic [7:0]  comp_hi,
  input  logic [7:0]  comp_lo
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // X-safety: when inputs are 2-state, all derived signals must be 2-state
  assert property ( !$isunknown({in,en1,en2}) |-> !$isunknown({comp_hi,comp_lo,dec1_out,dec2_out,out_hi,out_lo}) );

  // decoder1 gating and function
  assert property ( !$isunknown(en2) && !en2 |-> dec1_out == 4'h0 );
  assert property ( !$isunknown({en2,en1}) && en2
                    |-> dec1_out == {~en1[1], ~en1[0], en1[1], en1[0]} );

  // decoder2 gating and function (driven by dec1_out)
  assert property ( !$isunknown(en2) && !en2 |-> dec2_out == 16'h0000 );
  assert property ( !$isunknown({en2,dec1_out}) && en2
                    |-> dec2_out ==
                        { ~dec1_out[3], ~dec1_out[2], ~dec1_out[1], ~dec1_out[0],
                           dec1_out[3],  dec1_out[2],  dec1_out[1],  dec1_out[0],
                          ~dec1_out[3], ~dec1_out[2], ~dec1_out[1],  dec1_out[0],
                           dec1_out[3],  dec1_out[2],  dec1_out[1], ~dec1_out[0] } );

  // complement logic
  assert property ( !$isunknown(in[15:8]) |-> comp_hi == ~in[15:8] );
  assert property ( !$isunknown(in[7:0])  |-> comp_lo == ~in[7:0]  );

  // out_hi selection (en1 treated as boolean non-zero)
  assert property ( !$isunknown({en1,en2})
                    |-> out_hi == ((en1 != 2'b00) ? dec2_out[15:8] : 8'h00) );

  // out_lo selection between complements
  assert property ( !$isunknown({en1,in})
                    |-> out_lo == ((en1 != 2'b00) ? ~in[7:0] : ~in[15:8]) );

  // Functional coverage (concise but meaningful)
  cover property ( en2 && (en1 == 2'b00) );
  cover property ( en2 && (en1 == 2'b01) );
  cover property ( en2 && (en1 == 2'b10) );
  cover property ( en2 && (en1 == 2'b11) );
  cover property ( !en2 );
  cover property ( (en1 != 2'b00) && (in == 16'h0000) );
  cover property ( (en1 != 2'b00) && (in == 16'hFFFF) );
  cover property ( en2 && (en1 != 2'b00) && (dec2_out[15:8] != 8'h00) );

endmodule

// Example bind (edit clk/rst_n as appropriate):
// bind top_module top_module_sva sva ( .clk(tb_clk), .rst_n(tb_rst_n),
//   .in(in), .en1(en1), .en2(en2), .out_hi(out_hi), .out_lo(out_lo),
//   .dec1_out(dec1_out), .dec2_out(dec2_out), .comp_hi(comp_hi), .comp_lo(comp_lo) );