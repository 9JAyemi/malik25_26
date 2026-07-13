module sync_dff_en_W32 (clk, en, te, d, q);

  input clk, en, te;
  input [31:0] d;
  output reg [31:0] q;
  
  always @(posedge clk) begin
    if (en) begin
      if (te) begin
        q <= d;
      end else begin
        q <= #1 d;
      end
    end
  end

endmodule