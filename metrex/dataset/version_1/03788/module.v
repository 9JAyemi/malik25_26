
module sequence_detector (
  input in,
  output out,
  input clk,
  input reset
);

  // define your inputs and outputs here
  reg [1:0] state;
  parameter START = 2'b00;
  parameter FINAL = 2'b01;
  
  // define your states and transitions here
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      state <= START;
    end else begin
      case(state)
        START: begin
          if (in == 1'b1) begin
            state <= FINAL;
          end else begin
            state <= START;
          end
        end
        FINAL: begin
          if (in == 1'b0) begin
            state <= START;
          end else begin
            state <= FINAL;
          end
        end
      endcase
    end
  end
  
  // define your combinational logic circuit here
  assign out = (state == FINAL);
endmodule