module modified_decade_counter (
  input clk,
  input reset,
  input control,
  output reg [3:0] count
);

  reg [3:0] next_count;

  always @(posedge clk) begin
    if (reset) begin
      count <= 4'b0001;
    end else begin
      if (control) begin
        if (count == 4'b0101) begin
          next_count = 4'b0001;
        end else begin
          next_count = count + 1;
        end
      end else begin
        if (count == 4'b1010) begin
          next_count = 4'b0110;
        end else begin
          next_count = count + 1;
        end
      end
      if (count == 4'b1010) begin
        count <= 4'b0001;
      end else begin
        count <= next_count;
      end
    end
  end

endmodule
