module shift_register_ring_counter (input clk, input d, output reg q);

  reg [2:0] shift_reg;

  always @(posedge clk)
    shift_reg <= {shift_reg[1:0], d};

  always @*
    q = shift_reg[2];

endmodule