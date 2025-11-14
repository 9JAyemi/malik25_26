
module binary_counter #(
  parameter WIDTH = 4
) (
  // Input signals
  input clk,
  input reset, // Active low reset
  input count_up, // Active high count up input
  input count_down, // Active high count down input
  // Output signals
  output reg [WIDTH-1:0] count_out
);

  // State definition
  localparam INIT = 2'b00;
  localparam COUNT_UP = 2'b01;
  localparam COUNT_DOWN = 2'b10;
  localparam RESET = 2'b11;

  // State register and next state logic
  reg [1:0] state_reg, state_next;
  always @(posedge clk, negedge reset) begin
    if (!reset) begin
      state_reg <= INIT;
    end else begin
      state_reg <= state_next;
    end
  end

  // Output logic
  always @(posedge clk) begin
    case (state_reg)
      INIT: count_out <= {WIDTH{1'b0}};
      COUNT_UP: count_out <= count_out + 1'b1;
      COUNT_DOWN: count_out <= count_out - 1'b1;
      RESET: count_out <= {WIDTH{1'b0}};
    endcase
  end

  // Next state logic
  always @(*) begin
    case (state_reg)
      INIT: begin
        if (count_up) begin
          state_next = COUNT_UP;
        end else if (count_down) begin
          state_next = COUNT_DOWN;
        end else begin
          state_next = INIT;
        end
      end
      COUNT_UP: begin
        if (count_up) begin
          state_next = COUNT_UP;
        end else if (count_out == {WIDTH{1'b1}}) begin
          state_next = INIT;
        end else begin
          state_next = COUNT_UP;
        end
      end
      COUNT_DOWN: begin
        if (count_down) begin
          state_next = COUNT_DOWN;
        end else if (count_out == {WIDTH{1'b0}}) begin
          state_next = INIT;
        end else begin
          state_next = COUNT_DOWN;
        end
      end
      RESET: begin
        state_next = RESET;
      end
    endcase
  end

endmodule