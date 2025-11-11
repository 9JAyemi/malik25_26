module binary_to_bcd_converter (
  input clk,
  input reset,
  input [3:0] binary_input,
  output reg [3:0] msd_output,
  output reg [3:0] lsd1_output,
  output reg [3:0] lsd2_output
);

  always @(posedge clk) begin
    if (reset) begin
      msd_output <= 4'b0000;
      lsd1_output <= 4'b0000;
      lsd2_output <= 4'b0000;
    end else begin
      case (binary_input)
        4'b0000: begin
          msd_output <= 4'b0000;
          lsd1_output <= 4'b0000;
          lsd2_output <= 4'b0000;
        end
        4'b0001: begin
          msd_output <= 4'b0000;
          lsd1_output <= 4'b0000;
          lsd2_output <= 4'b0001;
        end
        4'b0010: begin
          msd_output <= 4'b0000;
          lsd1_output <= 4'b0001;
          lsd2_output <= 4'b0000;
        end
        4'b0011: begin
          msd_output <= 4'b0000;
          lsd1_output <= 4'b0001;
          lsd2_output <= 4'b0001;
        end
        4'b0100: begin
          msd_output <= 4'b0000;
          lsd1_output <= 4'b0010;
          lsd2_output <= 4'b0000;
        end
        4'b0101: begin
          msd_output <= 4'b0000;
          lsd1_output <= 4'b0010;
          lsd2_output <= 4'b0001;
        end
        4'b0110: begin
          msd_output <= 4'b0000;
          lsd1_output <= 4'b0011;
          lsd2_output <= 4'b0000;
        end
        4'b0111: begin
          msd_output <= 4'b0000;
          lsd1_output <= 4'b0011;
          lsd2_output <= 4'b0001;
        end
        4'b1000: begin
          msd_output <= 4'b0001;
          lsd1_output <= 4'b0000;
          lsd2_output <= 4'b0000;
        end
        4'b1001: begin
          msd_output <= 4'b0001;
          lsd1_output <= 4'b0000;
          lsd2_output <= 4'b0001;
        end
        4'b1010: begin
          msd_output <= 4'b0001;
          lsd1_output <= 4'b0001;
          lsd2_output <= 4'b0000;
        end
        4'b1011: begin
          msd_output <= 4'b0001;
          lsd1_output <= 4'b0001;
          lsd2_output <= 4'b0001;
        end
        4'b1100: begin
          msd_output <= 4'b0001;
          lsd1_output <= 4'b0010;
          lsd2_output <= 4'b0000;
        end
        4'b1101: begin
          msd_output <= 4'b0001;
          lsd1_output <= 4'b0010;
          lsd2_output <= 4'b0001;
        end
        4'b1110: begin
          msd_output <= 4'b0001;
          lsd1_output <= 4'b0011;
          lsd2_output <= 4'b0000;
        end
        4'b1111: begin
          msd_output <= 4'b0001;
          lsd1_output <= 4'b0011;
          lsd2_output <= 4'b0001;
        end
      endcase
    end
  end

endmodule
