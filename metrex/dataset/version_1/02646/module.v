module shift_register_with_parallel_load (
  input clk,
  input load,
  input direction,
  input [511:0] data,
  output reg [511:0] q
);

  always @(posedge clk) begin
    if (load) begin
      q <= data;
    end else begin
      if (direction) begin
        q <= {1'b0, q[511:1]};
      end else begin
        q <= {q[510:0], 1'b0};
      end
    end
  end

endmodule
