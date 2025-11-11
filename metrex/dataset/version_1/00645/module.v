module shift_register_control (
  input clk,
  input reset,
  input [3:0] input_value,
  output reg [15:0] output_value
);

  // Define states
  parameter IDLE = 2'b00;
  parameter WAIT_PATTERN = 2'b01;
  parameter OUTPUT_ENABLED = 2'b10;

  reg [1:0] state = IDLE;
  reg [3:0] shift_reg = 4'b0000;
  reg [3:0] pattern = 4'b0101;
  reg [3:0] count = 4'b0000;

  always @(posedge clk) begin
    if (reset) begin
      state <= IDLE;
      shift_reg <= 4'b0000;
      count <= 4'b0000;
      output_value <= 16'b0000000000000000;
    end
    else begin
      case (state)
        IDLE: begin
          if (input_value == pattern) begin
            state <= WAIT_PATTERN;
          end
        end
        WAIT_PATTERN: begin
          if (input_value != pattern) begin
            state <= IDLE;
            shift_reg <= 4'b0000;
            count <= 4'b0000;
          end
          else if (count == 4'b0011) begin
            state <= OUTPUT_ENABLED;
            count <= 4'b0000;
          end
          else begin
            count <= count + 4'b0001;
          end
        end
        OUTPUT_ENABLED: begin
          if (count == 4'b0011) begin
            state <= IDLE;
            shift_reg <= 4'b0000;
            count <= 4'b0000;
          end
          else begin
            shift_reg <= {shift_reg[2:0], input_value};
            count <= count + 4'b0001;
          end
        end
        default: state <= IDLE;
      endcase

      if (state == OUTPUT_ENABLED) begin
        output_value <= {shift_reg, 12'b000000000000};
      end
      else begin
        output_value <= 16'b0000000000000000;
      end
    end
  end

endmodule
