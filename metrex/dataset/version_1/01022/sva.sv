// SVA for font_decoder
// Assumes intended 32-bit key values (32'h0000_0001 ... 32'h0000_0009)
module font_decoder_sva (
  input logic [31:0] font_data_in,
  input logic [27:0] seg_out
);
  timeunit 1ns/1ps;
  default clocking cb @(posedge $global_clock); endclocking

  localparam int N = 9;

  localparam logic [31:0] VALS [N] = '{
    32'h0000_0001, 32'h0000_0002, 32'h0000_0003, 32'h0000_0004, 32'h0000_0005,
    32'h0000_0006, 32'h0000_0007, 32'h0000_0008, 32'h0000_0009
  };

  localparam logic [27:0] SEGS [N] = '{
    {7'b0111111, 7'b0000110, 7'b1011011, 7'b1001111},
    {7'b0000110, 7'b0000110, 7'b1111101, 7'b0000111},
    {7'b1011011, 7'b0000110, 7'b1101101, 7'b1001111},
    {7'b1001110, 7'b1100110, 7'b0000110, 7'b0000111},
    {7'b1111101, 7'b1101101, 7'b0000110, 7'b1001111},
    {7'b1111111, 7'b1101101, 7'b0000110, 7'b1001111},
    {7'b0000111, 7'b0000110, 7'b1011011, 7'b0000111},
    {7'b1111111, 7'b1101111, 7'b0000110, 7'b1001111},
    {7'b1111101, 7'b1101101, 7'b0000110, 7'b1001111}
  };

  function automatic bit in_set(input logic [31:0] v);
    bit hit = 0;
    for (int i=0;i<N;i++) if (v==VALS[i]) hit = 1;
    return hit;
  endfunction

  function automatic bit out_legal(input logic [27:0] s);
    bit hit = (s==28'b0);
    for (int i=0;i<N;i++) if (s==SEGS[i]) hit = 1;
    return hit;
  endfunction

  // Known output when input known
  assert property ( !$isunknown(font_data_in) |-> !$isunknown(seg_out) )
    else $error("font_decoder: seg_out has X/Z when font_data_in is known");

  // Mapping checks and per-code coverage
  genvar i;
  generate
    for (i=0;i<N;i++) begin : map_chk
      assert property ( (font_data_in==VALS[i]) |-> (seg_out==SEGS[i]) )
        else $error("font_decoder: seg_out mismatch for font_data_in=0x%08h", VALS[i]);
      cover property ( (font_data_in==VALS[i]) && (seg_out==SEGS[i]) );
    end
  endgenerate

  // Default mapping for all other inputs
  assert property ( !in_set(font_data_in) |-> (seg_out==28'b0) )
    else $error("font_decoder: unexpected seg_out for unmapped font_data_in=0x%08h", font_data_in);
  cover property ( !in_set(font_data_in) && seg_out==28'b0 );

  // Output must be in legal set
  assert property ( out_legal(seg_out) )
    else $error("font_decoder: seg_out not a legal encoding: 0x%07h", seg_out);

  // Combinational sanity: stable input implies stable output across sample points
  assert property ( $stable(font_data_in) |-> $stable(seg_out) )
    else $error("font_decoder: seg_out changed while font_data_in stable");
endmodule

bind font_decoder font_decoder_sva sva_font_decoder (.*);