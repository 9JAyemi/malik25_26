module shift_register_counter (
  input clk,
  input reset,
  input d,
  input select,
  output reg q
);

  reg [2:0] shift_reg;
  reg [1:0] counter;

  always @(posedge clk) begin
    if (reset) begin
      shift_reg <= 3'b000;
      counter <= 2'b00;
    end else begin
      if (select) begin
        // Shift register is active
        shift_reg <= {shift_reg[1:0], d};
        q <= shift_reg[2];
      end else begin
        // Counter is active
        counter <= counter + 1;
        q <= counter;
      end
    end
  end

endmodule

module top_module (
  input clk,
  input reset,
  input d,
  input select,
  output q
);

  shift_register_counter src (
    .clk(clk),
    .reset(reset),
    .d(d),
    .select(select),
    .q(q)
  );

endmodule