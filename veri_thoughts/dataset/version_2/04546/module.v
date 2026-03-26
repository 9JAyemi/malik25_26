module pipelined_JC_counter(
  input                clk,
  input                rst_n,
  output reg  [3:0]    Q
);

  reg [63:0] shift_reg;
  wire [3:0] feedback;

  assign feedback = {shift_reg[0], shift_reg[15], shift_reg[30], shift_reg[45]};

  always @(posedge clk) begin
    if (!rst_n) begin
      shift_reg <= 64'h0000000000000000;
      Q <= 4'b0000;
    end else begin
      shift_reg <= {shift_reg[62:0], feedback};
      Q <= shift_reg[63:60];
    end
  end

endmodule