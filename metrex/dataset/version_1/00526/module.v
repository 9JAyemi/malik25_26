
module register #(parameter WIDTH = 8, parameter RESET_VALUE = 0)
  (input [WIDTH-1:0] DataIn,
   input Write,
   input Clk,
   input Reset,
   input SyncReset,
   output [WIDTH-1:0] DataOut);

  reg [WIDTH-1:0] DataOut;

  always @(posedge Clk or posedge Reset or posedge SyncReset) begin
    if (Reset) begin
      DataOut <= RESET_VALUE;
    end else if (SyncReset) begin
      DataOut <= RESET_VALUE;
    end else if (Write) begin
      DataOut <= DataIn;
    end
  end

endmodule