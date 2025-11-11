module vending_machine(
  input clk,
  input reset,
  input quarter,
  input button_a,
  input button_b,
  input button_c,
  output reg dispense,
  output reg product_a,
  output reg product_b,
  output reg product_c
);

  parameter WAIT = 2'd0;
  parameter INSERTED = 2'd1;
  parameter DISPENSED = 2'd2;

  reg [1:0] state;
  reg [1:0] product;

  always @(posedge clk) begin
    if (reset) begin
      state <= WAIT;
      product <= 2'b0;
      dispense <= 1'b0;
      product_a <= 1'b0;
      product_b <= 1'b0;
      product_c <= 1'b0;
    end else begin
      case (state)
        WAIT: begin
          if (button_a) begin
            product <= 2'b01;
            state <= INSERTED;
          end else if (button_b) begin
            product <= 2'b10;
            state <= INSERTED;
          end else if (button_c) begin
            product <= 2'b11;
            state <= INSERTED;
          end
        end
        INSERTED: begin
          if (quarter) begin
            state <= (product == 2'b01 || product == 2'b10 || product == 2'b11) ? DISPENSED : INSERTED;
          end
        end
        DISPENSED: begin
          dispense <= 1'b1;
          case (product)
            2'b01: product_a <= 1'b1;
            2'b10: product_b <= 1'b1;
            2'b11: product_c <= 1'b1;
          endcase
          state <= WAIT;
        end
      endcase
    end
  end
endmodule