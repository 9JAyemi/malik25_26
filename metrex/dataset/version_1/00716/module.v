module d_ff_pre (
  input wire D,
  input wire C,
  input wire PRE,
  output reg Q
);

  always @ (posedge C or posedge PRE) begin
    if (PRE) begin
      Q <= 1'b1;
    end else begin
      Q <= D;
    end
  end

endmodule