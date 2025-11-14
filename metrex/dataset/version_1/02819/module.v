
module FFType_546(
  input         clock,
  input         reset,
  input  [39:0] io_in,
  output [39:0] io_out,
  input         io_enable
);

  // Register flip-flops
  reg [39:0] ff_reg;

  // Combinational logic
  assign io_out = (io_enable) ? ff_reg : io_in;

  // Sequential logic
  always @(posedge clock) begin
    if (reset) begin
      ff_reg <= 0;
    end else begin
      if (io_enable) begin
        ff_reg <= io_in;
      end
    end
  end

endmodule