module shift_register ( input clk, input d, output q );
  reg [2:0] reg_q;
  always @(posedge clk) begin
    reg_q <= {reg_q[1:0], d};
  end
  assign q = reg_q[2];
endmodule