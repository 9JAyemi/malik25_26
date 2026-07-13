
module flip_flops (
  input D, J, K, T, S, R, CLK,
  output Q_D, Q_JK, Q_T, Q_SR
);

// D flip-flop (positive edge-triggered)
reg Q_D;
always @(posedge CLK) begin
  Q_D <= D;
end

// JK flip-flop (negative edge-triggered)
reg Q_JK;
always @(negedge CLK) begin
  case({J, K})
    2'b00: Q_JK <= Q_JK;
    2'b01: Q_JK <= 0;
    2'b10: Q_JK <= 1;
    2'b11: Q_JK <= ~Q_JK;
  endcase
end

// T flip-flop (positive edge-triggered)
reg Q_T;
always @(posedge CLK) begin
  if (T) begin
    Q_T <= ~Q_T;
  end
end

// SR flip-flop (negative edge-triggered)
reg Q_SR;
always @(negedge CLK) begin
  case({S, R})
    2'b00: Q_SR <= Q_SR;
    2'b01: Q_SR <= 0;
    2'b10: Q_SR <= 1;
    2'b11: Q_SR <= 'bx; // undefined state
  endcase
end

endmodule