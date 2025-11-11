module gray_code_state_machine (
  input clk,
  input rst,
  output [n-1:0] out
);

parameter n = 4; // number of output signals

reg [n-1:0] state;
reg [n-1:0] gray_code;

always @ (posedge clk) begin
  if (rst) begin
    state <= 0;
  end else begin
    state <= gray_code;
  end
end

always @* begin
  case (state)
    0: gray_code = 0;
    1: gray_code = 1;
    2: gray_code = 3;
    3: gray_code = 2;
    4: gray_code = 6;
    5: gray_code = 7;
    6: gray_code = 5;
    7: gray_code = 4;
    default: gray_code = 0;
  endcase
end

assign out = gray_code;

endmodule