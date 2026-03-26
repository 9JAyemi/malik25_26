
module state_machine (
  input clk,
  input rst,
  input inp,
  output reg [31:0] outp
);

  // Define the two states
  parameter IDLE = 2'b00;
  parameter ACTIVE = 2'b01;

  // Define the state register
  reg [1:0] state;

  // Define the count register
  reg [31:0] count;

  // Define the state machine
  always @(posedge clk, posedge rst) begin
    if (rst) begin
      state <= IDLE;
      count <= 0;
    end else begin
      case(state)
        IDLE: begin
          if (inp) begin
            state <= ACTIVE;
            count <= 0;
          end
        end
        ACTIVE: begin
          if (inp) begin
            count <= count + 1;
          end else begin
            state <= IDLE;
          end
        end
      endcase
    end
  end

  // Define the output
  always @* begin
    if (state == ACTIVE) begin
      outp <= count;
    end else begin
      outp <= 0;
    end
  end

endmodule