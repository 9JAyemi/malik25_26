module shift_register #
  (
   parameter WIDTH = 16
  )
  (
   input clk,
   input load,
   input [WIDTH-1:0] data_in,
   input shift,
   input reset,
   output [WIDTH-1:0] data_out
  );

  reg [WIDTH-1:0] reg_data;

  always @(posedge clk) begin
    if (reset) begin
      reg_data <= {WIDTH{1'b0}};
    end else if (load) begin
      reg_data <= data_in;
    end else if (shift) begin
      reg_data <= {reg_data[WIDTH-2:0], 1'b0};
    end
  end

  assign data_out = reg_data;

endmodule