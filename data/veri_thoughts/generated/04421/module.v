module RegisterAnd
  (
    input EN,
    input [3:0] D,
    input CLK,
    output reg Q_AND
  );

  reg [3:0] Q;

  // Implement a 4-bit register with synchronous clear
  always @(posedge CLK)
  begin
    if (EN)
    begin
      Q <= D;
    end
    else
    begin
      Q <= 4'b0;
    end
  end

  // Implement the logical AND of the register's four bits
  always @*
  begin
    Q_AND = Q[0] & Q[1] & Q[2] & Q[3];
  end

endmodule