
module cycloneive_dffe(
  input D, CLK, ENA, CLRN, PRN,
  output reg Q
);

  always @(posedge CLK or negedge CLRN) begin
    if (CLRN == 0) begin
      Q <= 1'b0;
    end else begin
      if (ENA) begin
        if (PRN) begin
          Q <= 1'b1;
        end else begin
          Q <= D;
        end
      end
    end
  end

endmodule