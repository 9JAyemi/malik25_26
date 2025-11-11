module vending_machine (
  input clk,
  input reset,
  input coin,
  input button,
  output reg dispense
);

  // Define the states
  parameter IDLE = 2'b00;
  parameter WAITING = 2'b01;
  parameter DISPENSING = 2'b10;

  // Define the drinks
  parameter COKE = 2'b00;
  parameter SPRITE = 2'b01;
  parameter FANTA = 2'b10;

  // Define the state and drink variables
  reg [1:0] state, next_state;
  reg [1:0] drink, next_drink;

  // Define the counter variables
  reg [3:0] press_count;
  reg [3:0] coin_count;

  // Initialize the variables
  initial begin
    state = IDLE;
    drink = COKE;
    press_count = 0;
    coin_count = 0;
    dispense = 0;
  end

  // Define the state transition and output logic
  always @(posedge clk) begin
    if (reset) begin
      state <= IDLE;
      drink <= COKE;
      press_count <= 0;
      coin_count <= 0;
      dispense <= 0;
    end else begin
      // Update the state and drink variables
      state <= next_state;
      drink <= next_drink;

      // Update the counter variables
      press_count <= (state == WAITING) ? (press_count + 1) : 0;
      coin_count <= (state == WAITING) ? (coin_count + 1) : 0;

      // Update the output variable
      dispense <= (state == DISPENSING);

      // Define the next state and drink based on the current state and inputs
      case (state)
        IDLE: begin
          next_state = coin ? WAITING : IDLE;
          next_drink = COKE;
        end
        WAITING: begin
          next_state = (press_count >= 5) ? DISPENSING : (coin_count >= 10) ? IDLE : WAITING;
          next_drink = (button) ? ((coin) ? FANTA : SPRITE) : drink;
        end
        DISPENSING: begin
          next_state = IDLE;
          next_drink = COKE;
        end
      endcase
    end
  end

endmodule