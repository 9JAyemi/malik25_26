module comparator_4bit_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic [1:0] result
);

  // The logic is purely combinational, so we use @(posedge clk) for assertions.

  // The result should be 2'b01 when A > B.
  greater_than: assert property (
    @(posedge clk) (A > B) |-> (result == 2'b01)
  );

  // The result should be 2'b10 when A < B.
  less_than: assert property (
    @(posedge clk) (A < B) |-> (result == 2'b10)
  );

  // The result should be 2'b00 when A == B.
  equal: assert property (
    @(posedge clk) (A == B) |-> (result == 2'b00)
  );

endmodule