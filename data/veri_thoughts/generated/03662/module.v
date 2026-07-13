
module TLATCH (
  input E, SE, CK, D,
  output ECK
);

  reg d;
  always @(posedge CK or negedge E) begin
    if (!E) begin
      d <= 1'b0;
    end else begin
      if (SE) begin
        d <= D;
      end
    end
  end

  assign ECK = E & d;

endmodule
