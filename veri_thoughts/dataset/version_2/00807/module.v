module next_state_logic (
  input x,
  input [2:0] y,
  output Y2
);

reg Y2;

always @(*) begin
  case (y)
    3'b000: Y2 = x;
    3'b001: Y2 = 0;
    3'b010: Y2 = x;
    3'b011: Y2 = 1;
    3'b100: Y2 = 1;
    3'b101: Y2 = x;
    default: Y2 = 0;
  endcase
end

endmodule
