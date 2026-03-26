
module shift_register ( input clk, input d, output reg q );

  always @(posedge clk)
    q <= {q, d};

endmodule
