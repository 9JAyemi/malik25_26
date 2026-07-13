module decoder_2to4_sva (
  input logic clk,              // sampling clock for assertions (RTL has no clock)
  input logic [1:0] in_data,    // DUT input
  input logic [3:0] out_data    // DUT output
);
  // RTL: no reset, purely combinational 2->4 one-hot decoder with default to 0000 on unknown input

  // Input 00 decodes to 0001.
  decode_map_00: assert property (
    @(posedge clk) disable iff ($initstate) (in_data == 2'b00) |-> (out_data == 4'b0001)
  );

  // Input 01 decodes to 0010.
  decode_map_01: assert property (
    @(posedge clk) disable iff ($initstate) (in_data == 2'b01) |-> (out_data == 4'b0010)
  );

  // Input 10 decodes to 0100.
  decode_map_10: assert property (
    @(posedge clk) disable iff ($initstate) (in_data == 2'b10) |-> (out_data == 4'b0100)
  );

  // Input 11 decodes to 1000.
  decode_map_11: assert property (
    @(posedge clk) disable iff ($initstate) (in_data == 2'b11) |-> (out_data == 4'b1000)
  );

  // Output 0001 implies known input 00.
  reverse_map_0001: assert property (
    @(posedge clk) disable iff ($initstate) (!$isunknown(in_data) && (out_data == 4'b0001)) |-> (in_data == 2'b00)
  );

  // Output 0010 implies known input 01.
  reverse_map_0010: assert property (
    @(posedge clk) disable iff ($initstate) (!$isunknown(in_data) && (out_data == 4'b0010)) |-> (in_data == 2'b01)
  );

  // Output 0100 implies known input 10.
  reverse_map_0100: assert property (
    @(posedge clk) disable iff ($initstate) (!$isunknown(in_data) && (out_data == 4'b0100)) |-> (in_data == 2'b10)
  );

  // Output 1000 implies known input 11.
  reverse_map_1000: assert property (
    @(posedge clk) disable iff ($initstate) (!$isunknown(in_data) && (out_data == 4'b1000)) |-> (in_data == 2'b11)
  );

  // Known input must produce a one-hot output.
  known_in_onehot_out: assert property (
    @(posedge clk) disable iff ($initstate) (!$isunknown(in_data)) |-> $onehot(out_data)
  );

  // Unknown input forces output to 0000 (default case).
  unknown_in_zero_out: assert property (
    @(posedge clk) disable iff ($initstate) $isunknown(in_data) |-> (out_data == 4'b0000)
  );

endmodule