module register_32bit_parallel_load (
  input CLK,
  input AR,
  input E,
  input [31:0] O,
  output reg [31:0] Q,
  output reg Overflow_flag_A
);

  always @(posedge CLK or negedge AR) begin
    if (!AR) begin // asynchronous reset
      Q <= 0;
      Overflow_flag_A <= 0;
    end else if (E) begin // parallel load
      Q <= O;
      Overflow_flag_A <= 0;
    end else begin // hold
      Overflow_flag_A <= (Q == 32'hFFFFFFFF);
    end
  end

endmodule