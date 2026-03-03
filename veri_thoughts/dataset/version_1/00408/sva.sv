// SVA for decoder and split_16bit_input

// Assertions for decoder: out must equal in; cover all encodings
module decoder_sva(input logic [1:0] in, input logic [1:0] out);
  assert property (@(in or out) out == in);
  assert property (@(in or out) disable iff ($isunknown(in)) !$isunknown(out));

  cover property (@(in) in == 2'b00);
  cover property (@(in) in == 2'b01);
  cover property (@(in) in == 2'b10);
  cover property (@(in) in == 2'b11);
endmodule

// Assertions for split_16bit_input
module split_16bit_input_sva(
  input logic [15:0] in,
  input logic [7:0]  out_hi,
  input logic [7:0]  out_lo,
  input logic [1:0]  select,
  input logic [1:0]  decoder_out
);
  // Internal connectivity and mux behavior
  assert property (@(in or select)               select      == {1'b0, in[15]});
  assert property (@(select or decoder_out)      decoder_out == select);
  assert property (@(in or decoder_out or out_hi) out_hi     == (in[15] ? in[15:8] : in[7:0]));
  assert property (@(in or decoder_out or out_lo) out_lo     == in[7:0]);

  // Knownness when inputs are known
  assert property (@(in or out_hi or out_lo or select or decoder_out)
                   disable iff ($isunknown(in)) !$isunknown({out_hi,out_lo,select,decoder_out}));

  // Functional coverage: both select paths exercised for out_hi; out_lo always low byte
  cover property (@(in) (in[15]==1'b0) && (out_hi==in[7:0])  && (out_lo==in[7:0]));
  cover property (@(in) (in[15]==1'b1) && (out_hi==in[15:8]) && (out_lo==in[7:0]));
endmodule

// Bind assertions
bind decoder            decoder_sva            u_decoder_sva (.in(in), .out(out));
bind split_16bit_input  split_16bit_input_sva u_split_sva    (.in(in), .out_hi(out_hi), .out_lo(out_lo),
                                                              .select(select), .decoder_out(decoder_out));