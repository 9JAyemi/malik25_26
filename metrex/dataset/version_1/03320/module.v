module chatgpt_generate_edge_detect(
  input               clk,
  input               rst_n,
  input               a,
  output reg          rise,
  output reg          down
);

  // Define the states for the state machine
  parameter IDLE = 2'b00;
  parameter RISING_EDGE = 2'b01;
  parameter FALLING_EDGE = 2'b10;

  // Define the current state and next state variables
  reg [1:0] current_state, next_state;

  // Initialize the current state to IDLE
  initial current_state = IDLE;

  // Detect rising and falling edges
  always @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      current_state <= IDLE;
      rise <= 1'b0;
      down <= 1'b0;
    end
    else begin
      current_state <= next_state;
      case (current_state)
        IDLE: begin
          if (a == 1'b1) begin
            next_state = RISING_EDGE;
          end
          else if (a == 1'b0) begin
            next_state = FALLING_EDGE;
          end
          else begin
            next_state = IDLE;
          end
          rise <= 1'b0;
          down <= 1'b0;
        end
        RISING_EDGE: begin
          next_state = IDLE;
          rise <= 1'b1;
          down <= 1'b0;
        end
        FALLING_EDGE: begin
          next_state = IDLE;
          rise <= 1'b0;
          down <= 1'b1;
        end
        default: begin
          next_state = IDLE;
          rise <= 1'b0;
          down <= 1'b0;
        end
      endcase
    end
  end

endmodule