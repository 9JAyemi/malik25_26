
module dffe (
   Q,
   CLK,
   ENA,
   D,
   CLRN,
   PRN
);
   input D;
   input CLK;
   input CLRN, PRN;
   input ENA;
   output Q;

   reg Q_reg = 1'b0;

   always @(posedge CLK) begin
      if (CLRN == 1'b0) begin
         Q_reg <= 1'b0;
      end
      else if (PRN == 1'b0) begin
         Q_reg <= 1'b1;
      end
      else if (ENA) begin
         Q_reg <= D;
      end
   end

   assign Q = Q_reg;
endmodule