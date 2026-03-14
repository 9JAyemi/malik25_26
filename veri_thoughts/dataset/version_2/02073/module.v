module chatgpt_generate_JC_counter(
  input                clk,
  input                rst_n,
  output reg  [63:0]   Q
);

  reg [63:0] lfsr;
  
  always @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      lfsr <= 64'h0000000000000000;
      Q <= 4'b0000;
    end
    else begin
      lfsr <= {lfsr[62:0], lfsr[63] ^ lfsr[0] ^ lfsr[3] ^ lfsr[4]};
      Q <= {lfsr[0], lfsr[4], lfsr[5], lfsr[6]};
    end
  end
  
endmodule