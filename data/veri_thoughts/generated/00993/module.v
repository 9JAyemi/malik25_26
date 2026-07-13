module bcd_counter (
  input clk,
  input reset,
  input [2:0] enable,
  output reg [9:0] q
);

  always @(posedge clk) begin
    if (reset) begin
      q <= 10'd0;
    end else if (enable[2]) begin
      if (q[9:6] == 4'd9) begin
        q[9:6] <= 4'd0;
        if (enable[1]) begin
          if (q[5:2] == 4'd9) begin
            q[5:2] <= 4'd0;
            if (enable[0]) begin
              if (q[1:0] == 2'd3) begin
                q[1:0] <= 2'd0;
              end else begin
                q[1:0] <= q[1:0] + 2'd1;
              end
            end
          end else begin
            q[5:2] <= q[5:2] + 4'd1;
          end
        end
      end else begin
        q[9:6] <= q[9:6] + 4'd1;
      end
    end
  end

endmodule
