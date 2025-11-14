module shift_register ( input clk, input serial_in, output serial_out );

  wire q0, q1, q2;

  d_flip_flop dff0 ( .clk(clk), .d(serial_in), .q(q0) );
  d_flip_flop dff1 ( .clk(clk), .d(q0), .q(q1) );
  d_flip_flop dff2 ( .clk(clk), .d(q1), .q(q2) );

  assign serial_out = q2;

endmodule

module d_flip_flop ( input clk, input d, output q );

  reg q;

  always @(posedge clk) begin
    q <= d;
  end

endmodule