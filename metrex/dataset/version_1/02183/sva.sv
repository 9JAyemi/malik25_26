// SVA for decoder_4to16_pipeline
// Bind this module to the DUT:
// bind decoder_4to16_pipeline decoder_4to16_pipeline_sva sva_i(.clk(clk), .select(select), .en(en), .out(out));

module decoder_4to16_pipeline_sva (
  input logic        clk,
  input logic [1:0]  select,
  input logic        en,
  input logic [15:0] out
);

  // Make $past safe from time 0
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Basic sanity
  a_inputs_known:  assert property (!$isunknown({en, select}));
  a_out_known:     assert property (!$isunknown(out));

  // Upper 12 bits are always 1
  a_upper_ones:    assert property (out[15:4] == 12'hFFF);

  // One-cycle pipelined functional mapping
  // If past en==1 -> all ones; else lower nibble is ~(1<<select), upper all ones
  a_functional: assert property (
    out == ($past(en)
            ? 16'hFFFF
            : {12'hFFF, ~(4'b0001 << $past(select))})
  );

  // When decode is active (past en==0), exactly one zero in lower nibble
  a_onehot_lower: assert property (
    !$past(en) |-> ($onehot(~out[3:0]) && out[15:4]==12'hFFF)
  );

  // Minimal functional coverage
  c_en_disabled:  cover property ( en ##1 out == 16'hFFFF );
  c_sel_00:       cover property ( !en ##1 out[3:0] == 4'b1110 );
  c_sel_01:       cover property ( !en ##1 out[3:0] == 4'b1101 );
  c_sel_10:       cover property ( !en ##1 out[3:0] == 4'b1011 );
  c_sel_11:       cover property ( !en ##1 out[3:0] == 4'b0111 );

endmodule