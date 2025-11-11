
module counter #(
  parameter M = 0
) (
  input clk,
  input rst,
  input cnt,
  output reg [31:0] q,
  output reg ov
);

  localparam N = M < 32 ? M : 32;

  always @(posedge clk) begin
    if (rst || ov) begin
      q <= 0;
      ov <= 0;
    end else begin
      if (cnt) begin
        q <= q + 1;
        if (q == M-1) begin
          ov <= 1;
        end
      end
    end
  end

endmodule