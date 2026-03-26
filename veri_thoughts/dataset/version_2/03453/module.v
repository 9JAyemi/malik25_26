
module shift_register(CLK, EN, TE, DATA_IN, DATA_OUT);
  input CLK, EN, TE, DATA_IN;

  output reg [3:0] DATA_OUT;

  always @(posedge CLK) begin
    if (EN) begin
      DATA_OUT <= {DATA_OUT[2:0], DATA_IN};
    end
  end

endmodule