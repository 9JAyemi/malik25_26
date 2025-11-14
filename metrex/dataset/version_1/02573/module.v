module fsm_sequence_detection (
  input clk,
  input reset,
  input [7:0] data,
  output reg match
);

  parameter S0 = 2'b00, S1 = 2'b01, S2 = 2'b10, S3 = 2'b11;
  reg [1:0] state, next_state;

  always @(posedge clk, posedge reset) begin
    if (reset) begin
      state <= S0;
      match <= 1'b0;
    end
    else begin
      state <= next_state;
      match <= (state == S3);
    end
  end

  always @(*) begin
    next_state = state;
    case(state)
      S0: if (data[7:4] == 4'b1010) next_state = S1;
      S1: if (data[7:4] == 4'b1010) next_state = S2;
          else next_state = S0;
      S2: if (data[7:4] == 4'b1010) next_state = S3;
          else next_state = S0;
      S3: next_state = S0;
    endcase
  end

endmodule
