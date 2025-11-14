module shift_register(
    input clk, 
    input shift, 
    input in,
    output reg out
);
  reg [3:0] reg_out;

  always @(posedge clk) begin
    if (shift) begin
      reg_out <= {reg_out[2:0], in};
    end else begin
      reg_out <= {in, reg_out[3:1]};
    end
  end

  always @*
    out = reg_out[0];
endmodule