
module sirv_aon_porrst(
  input  clk,
  output reg porrst_n
);

  reg [31:0] counter = 0;

  `ifdef FPGA_SOURCE
      // In FPGA, we have no PORRST circuit
      assign porrst_n = 1'b1;
  `else
      // Generate PORRST signal using circuit
      always @(posedge clk) begin
        if (counter < 100) begin
          counter <= counter + 1;
          porrst_n <= 1'b0;
        end else begin
          porrst_n <= 1'b1;
        end
      end
  `endif

endmodule
